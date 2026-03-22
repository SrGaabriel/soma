/*
 * Soma Runtime
 *
 * === Headerless Heap Objects ===
 *
 * After monomorphization, the compiler knows every type at every point.
 * Heap objects carry NO runtime headers — no tag byte, no magic sentinel,
 * no count field. Object identity and layout are determined entirely at
 * compile time via type-specialized erase/clone functions.
 *
 * All pointer-width values use `void*` or `sizeof(void*)` — the runtime
 * adapts automatically to 32-bit (wasm32) and 64-bit targets when compiled
 * with the appropriate -target flag.
 *
 * Tagged Payload (count * sizeof(void*) bytes):
 *   Pure data — the compiler-generated eraser knows field count/types.
 *
 * Closure (sizeof(SomaClosure) + env_size * sizeof(void*) bytes):
 *   [0]         u8    arity     (needed by soma_apply for PAP detection)
 *   [1..PAD-1]  u8    _pad      [0]=NODE_CLOSURE, [1..2]=env_size LE16, rest=alignment
 *   [PAD]       ptr   func_ptr  (function pointer)
 *   [PAD+PTR]   ptr   env[0]    ...
 *
 * String (fat pointer, 2 * sizeof(void*) bytes):
 *   ptr  data   (pointer to UTF-8 bytes, null-terminated)
 *   i64  len    (byte count; bit 63 = static sentinel)
 *
 * SUP (pool-allocated — keeps header for state machine):
 *   u8           tag        (SUP_TAG_*)
 *   u8[3]        _pad       ('S','U','P')
 *   u32          label
 *   ptr          value, proj0, proj1, type_desc
 *
 * Flat Array View (pool-allocated — keeps header for tag dispatch):
 *   u8/pad/u32   header
 *   i64          length
 *   ptr          data, backing
 */

#ifndef SOMA_RUNTIME_H
#define SOMA_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>

/*
 * Compiler intrinsics and attributes
 *
 * These macros abstract GCC/Clang-specific features with safe fallbacks.
 * They control branch prediction, code layout, alias analysis, and
 * alignment — all critical for a high-performance allocator + eval/apply.
 *
 * SOMA_HOT / SOMA_COLD:
 *   Control function placement. HOT functions are grouped into .text.hot
 *   (better I-cache density); COLD functions are pushed away to avoid
 *   polluting hot pages. GCC/Clang also raise inline thresholds for HOT.
 *
 * SOMA_MALLOC:
 *   Returned pointer doesn't alias any existing pointer. Enables the
 *   compiler to eliminate redundant loads after allocation in callers.
 *
 * SOMA_FLATTEN:
 *   Force-inline all callees. Used on soma_apply to create one large
 *   optimized function body — the single hottest path in eval/apply.
 */
#if defined(__GNUC__) || defined(__clang__)
#define SOMA_LIKELY(x)          __builtin_expect(!!(x), 1)
#define SOMA_UNLIKELY(x)        __builtin_expect(!!(x), 0)
#define SOMA_PREFETCH(p)        __builtin_prefetch(p)
#define SOMA_HOT                __attribute__((hot))
#define SOMA_COLD               __attribute__((cold))
#define SOMA_MALLOC             __attribute__((malloc))
#define SOMA_ALLOC_SIZE(...)    __attribute__((alloc_size(__VA_ARGS__)))
#define SOMA_NORETURN           __attribute__((noreturn))
#define SOMA_FLATTEN            __attribute__((flatten))
#define SOMA_NOINLINE           __attribute__((noinline))
#define SOMA_NONNULL(...)       __attribute__((nonnull(__VA_ARGS__)))
#define SOMA_WARN_UNUSED        __attribute__((warn_unused_result))
#define SOMA_ALIGNED(n)         __attribute__((aligned(n)))
#define SOMA_ASSUME_ALIGNED(p, a) __builtin_assume_aligned((p), (a))
#else
#define SOMA_LIKELY(x)          (x)
#define SOMA_UNLIKELY(x)        (x)
#define SOMA_PREFETCH(p)        ((void)0)
#define SOMA_HOT
#define SOMA_COLD
#define SOMA_MALLOC
#define SOMA_ALLOC_SIZE(...)
#define SOMA_NORETURN
#define SOMA_FLATTEN
#define SOMA_NOINLINE
#define SOMA_NONNULL(...)
#define SOMA_WARN_UNUSED
#define SOMA_ALIGNED(n)
#define SOMA_ASSUME_ALIGNED(p, a) (p)
#endif

#define SOMA_CACHELINE 64

/* Node tag constants */
#define NODE_CLOSURE          1   /* stored in closure _pad[0] for runtime identification */
#define NODE_FLAT_ARRAY       4
#define NODE_FLAT_ARRAY_VIEW  5
#define NODE_LIST_SEGMENT     6
#define NODE_LIST_NODE        7

/* SUP padding bytes for identification */
#define SOMA_SUP_PAD0 0x53u            /* 'S' */
#define SOMA_SUP_PAD1 0x55u            /* 'U' */
#define SOMA_SUP_PAD2 0x50u            /* 'P' */

/* Packed SUP magic for single-compare identification (little-endian: 'S','U','P') */
#define SOMA_SUP_MAGIC_U32 (((uint32_t)SOMA_SUP_PAD2 << 16) | \
                            ((uint32_t)SOMA_SUP_PAD1 << 8)  | \
                            ((uint32_t)SOMA_SUP_PAD0))

/*
 * Packed SUP header: tag + pad[0..2] as a single 32-bit value.
 * Used by soma_dup_typed to init the first 4 bytes in one store.
 * Little-endian layout: [SUP_TAG_FRESH, 'S', 'U', 'P']
 */
#define SOMA_SUP_HEADER_FRESH ((uint32_t)SUP_TAG_FRESH         \
                             | ((uint32_t)SOMA_SUP_PAD0 << 8)  \
                             | ((uint32_t)SOMA_SUP_PAD1 << 16) \
                             | ((uint32_t)SOMA_SUP_PAD2 << 24))

/*
 * SUP (Superposition) Node Tags
 *
 * SUP nodes implement lazy duplication for Tier 3 values (recursive data).
 * Instead of eagerly cloning, a DUP creates a SUP wrapping the value.
 * When projections access the SUP, cloning is deferred until both sides
 * are needed. Same-label DUP-SUP pairs annihilate in O(1).
 */
#define SUP_TAG_FRESH         0x80
#define SUP_TAG_PROJ0         0x81
#define SUP_TAG_PROJ1         0x82
#define SUP_TAG_BOTH          0x83
#define SUP_TAG_PROJ0_CLONING 0x84
#define SUP_TAG_PROJ1_CLONING 0x85

/* Check if a tag byte indicates a SUP node */
#define IS_SUP(tag)  (((tag) & 0x80) != 0)

/*
 * Tagged Pointer Representation
 *
 * Low bits of pointers for type tags (assuming pointer-aligned allocation).
 *
 * Pointer format:
 *   [MSB : TAG_BITS] payload  [TAG_BITS-1 : 0] tag
 *
 * Tag values:
 *   000 = Heap pointer (closure, etc.) - must be pointer-aligned
 *   001 = Small integer (shifted right by TAG_BITS)
 *   010 = Boolean/Unit (payload: 0=false, 1=true, 2=unit)
 *   011 = Character (payload: Unicode codepoint)
 */

#if UINTPTR_MAX == 0xFFFFFFFF
/* 32-bit: 2 tag bits (4-byte alignment) */
#define TAG_BITS        2
#define TAG_MASK        0x3UL
#define PAYLOAD_SHIFT   2
#else
/* 64-bit: 3 tag bits (8-byte alignment) */
#define TAG_BITS        3
#define TAG_MASK        0x7ULL
#define PAYLOAD_SHIFT   3
#endif

/* Tag values */
#define TAG_PTR         0   /* Heap pointer */
#define TAG_INT         1   /* Small integer */
#define TAG_BOOL        2   /* Boolean/Unit */
#define TAG_CHAR        3   /* Character */

/* Payload values for TAG_BOOL */
#define BOOL_FALSE      0
#define BOOL_TRUE       1
#define BOOL_UNIT       2

/* Type alias for tagged values */
typedef uintptr_t SomaValue;

/* Check tag */
#define SOMA_GET_TAG(v)      ((v) & TAG_MASK)
#define SOMA_IS_PTR(v)       (SOMA_GET_TAG(v) == TAG_PTR)
#define SOMA_IS_INT(v)       (SOMA_GET_TAG(v) == TAG_INT)
#define SOMA_IS_BOOL(v)      (SOMA_GET_TAG(v) == TAG_BOOL)
#define SOMA_IS_CHAR(v)      (SOMA_GET_TAG(v) == TAG_CHAR)

/* Extract pointer (assumes TAG_PTR) */
#define SOMA_TO_PTR(v)       ((void*)(v))

/* Create/extract small integer (intptr_t-width, sign-extended) */
#define SOMA_INT(n)          ((((SomaValue)(intptr_t)(n)) << PAYLOAD_SHIFT) | TAG_INT)
#define SOMA_TO_INT(v)       ((intptr_t)(v) >> PAYLOAD_SHIFT)

/* Create/extract boolean */
#define SOMA_FALSE           ((SomaValue)(BOOL_FALSE << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_TRUE            ((SomaValue)(BOOL_TRUE << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_UNIT            ((SomaValue)(BOOL_UNIT << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_TO_BOOL(v)      ((int)(((v) >> PAYLOAD_SHIFT) & 1))

/* Create/extract character */
#define SOMA_CHAR(c)         ((((SomaValue)(c)) << PAYLOAD_SHIFT) | TAG_CHAR)
#define SOMA_TO_CHAR(v)      ((uint32_t)((v) >> PAYLOAD_SHIFT))

/* Create pointer value (for heap objects) */
#define SOMA_PTR(p)          ((SomaValue)(p))

/*
 * Closure structure (env follows after func_ptr)
 *
 * _pad[0] = NODE_CLOSURE sentinel for runtime identification by soma_era_free.
 * _pad[1..2] = env_size as little-endian u16 (needed by soma_apply for PAP
 *   creation and by soma_era_closure for dynamic env traversal).
 *
 * Layout adapts to pointer width:
 *   64-bit: {u8, u8[7], ptr} = 16 bytes header
 *   32-bit: {u8, u8[3], ptr} =  8 bytes header
 */
typedef struct SomaClosure {
    uint8_t  arity;                       /* remaining args (needed by soma_apply) */
    uint8_t  _pad[sizeof(void*) - 1];    /* [0]=NODE_CLOSURE, [1..2]=env_size LE16, rest=reserved */
    void*    func_ptr;                    /* function pointer */
    /* void* env[] follows at offset 2*sizeof(void*) */
} SomaClosure;

/* Extract env_size from closure _pad[1..2] as little-endian u16 */
#define CLOSURE_ENV_SIZE(c) ((uint16_t)(c)->_pad[1] | ((uint16_t)(c)->_pad[2] << 8))

/*
 * Type-specialized function pointers for clone and erase.
 *
 * The compiler generates one clone and one erase function per concrete type.
 * A SomaTypeDesc bundles both into a single struct so SUP nodes only need
 * one pointer (8 bytes) instead of two (16 bytes). The TypeDesc structs are
 * emitted as static LLVM globals — no runtime allocation.
 */
typedef void* (*SomaCloneFn)(void* value, uint32_t label);
typedef void  (*SomaEraseFn)(void* value);

typedef struct SomaTypeDesc {
    SomaCloneFn  clone_fn;
    SomaEraseFn  erase_fn;
} SomaTypeDesc;

/*
 * SUP (Superposition) node structure (48 bytes, pool-allocated)
 */
typedef struct SomaSup {
    uint8_t       tag;
    uint8_t       _pad[3];
    uint32_t      label;
    void*         value;
    void*         proj0;
    void*         proj1;
    SomaTypeDesc* type_desc;
} SomaSup;

/*
 * String: fat pointer { data, len }.
 *
 * 16 bytes, passed/returned by value in two registers (x86-64: rax, rdx).
 * `data` always points to a valid null-terminated UTF-8 byte sequence.
 * The MSB of `len` is a static sentinel: static string globals emitted
 * by the compiler have bit 63 set, preventing soma_era_string from
 * freeing read-only memory.
 */
#define SOMA_STRING_STATIC_BIT ((int64_t)1 << 63)

typedef struct SomaString {
    char*    data;      /* pointer to UTF-8 bytes (null-terminated) */
    int64_t  len;       /* byte count; bit 63 = static sentinel */
} SomaString;

static inline int64_t soma_string_len(SomaString s) {
    return s.len & ~SOMA_STRING_STATIC_BIT;
}

/*
 * Flat array backing storage (compiler-generated, not user-facing)
 */
typedef struct SomaFlatArray {
    uint8_t   tag;         /* NODE_FLAT_ARRAY */
    uint8_t   elem_size;   /* bytes per element */
    uint8_t   _pad[2];
    uint32_t  _reserved;
    int64_t   length;
    /* element data follows at offset 16 */
} SomaFlatArray;

/*
 * Flat array view (user-facing list representation)
 */
typedef struct SomaFlatArrayView {
    uint8_t   tag;         /* NODE_FLAT_ARRAY_VIEW */
    uint8_t   _pad[3];
    uint32_t  _reserved;
    int64_t   length;
    void*     data;        /* pointer to first visible element */
    void*     backing;     /* owned backing SomaFlatArray (or NULL) */
} SomaFlatArrayView;

/*
 * Chunked list segment — refcounted contiguous storage for typed elements.
 * One cache line of data per segment by default (capacity = CACHELINE / elem_size).
 * The data region follows inline at offset 8.
 */
typedef struct SomaSegment {
    _Atomic uint32_t refcount;   /* shared ownership count */
    uint16_t capacity;           /* total element slots in data[] */
    uint16_t elem_size;          /* bytes per element (e.g. 4 for i32, 8 for ptr) */
    /* T data[capacity] follows at offset 8 */
} SomaSegment;

/*
 * List node — a view into a segment plus a link to the next node.
 * A list is a SomaListNode* (NULL = empty list / Nil).
 * Multiple nodes can share the same segment via refcounting.
 * 2*ptr + 2*u16 + u32 — fits in pool_48 on both 32-bit and 64-bit.
 */
typedef struct SomaListNode {
    SomaSegment*          segment;   /* owned segment (refcounted) */
    struct SomaListNode*  next;      /* next node in chain (or NULL) */
    uint16_t              start;     /* first valid element index in segment */
    uint16_t              end;       /* one past last valid element index */
    _Atomic uint32_t      refcount;  /* shared ownership count */
} SomaListNode;

/* Layout guards — catch struct packing surprises across compilers */
#if UINTPTR_MAX == 0xFFFFFFFF
/* 32-bit targets */
_Static_assert(sizeof(SomaClosure)      == 8,  "SomaClosure header must be 2*sizeof(void*)");
_Static_assert(sizeof(SomaSup)          <= 28, "SomaSup must fit pool_48");
_Static_assert(sizeof(SomaSegment)      == 8,  "SomaSegment header must be 8 bytes");
_Static_assert(sizeof(SomaListNode)     <= 20, "SomaListNode must fit pool_48");
#else
/* 64-bit targets */
_Static_assert(sizeof(SomaClosure)      == 16, "SomaClosure header must be 2*sizeof(void*)");
_Static_assert(sizeof(SomaSup)          == 48
            || sizeof(SomaSup)          == 40, "SomaSup must fit pool_48");
_Static_assert(sizeof(SomaFlatArrayView) == 32, "View must fit pool_48");
_Static_assert(sizeof(SomaFlatArray)    == 16, "FlatArray header must be 16 bytes");
_Static_assert(sizeof(SomaSegment)      == 8,  "SomaSegment header must be 8 bytes");
_Static_assert(sizeof(SomaListNode)     == 24, "SomaListNode must fit pool_48");
#endif


/*
 * Core runtime functions
 */

SOMA_HOT void soma_era_free(void* value);

SOMA_NORETURN SOMA_COLD void soma_panic(const char* msg);

/*
 * String operations
 */

/* to_cstring: returns the data pointer directly (identity for null-terminated strings) */
static inline char* soma_to_cstring(SomaString str) { return str.data; }

/* from_cstring: allocates a new SomaString from a C string */
SOMA_WARN_UNUSED
SomaString soma_from_cstring(const char* cstr);

/* strcat: concatenates two strings, allocating a new buffer */
SOMA_WARN_UNUSED SOMA_HOT
SomaString soma_strcat(SomaString a, SomaString b);

/* int_to_string: format i32 as decimal string */
SOMA_WARN_UNUSED
SomaString soma_int_to_string(int32_t val);

/* era_string: free string data if heap-allocated (not static) */
void soma_era_string(SomaString str);

/*
 * Flat array view operations (legacy — used for Array, not List)
 */

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_HOT
void* soma_clone_flat_array_view(SomaFlatArrayView* src);

/*
 * Chunked list operations
 *
 * Lists are represented as SomaListNode* (NULL = Nil).
 * All operations are O(1). Cons exploits linear ownership (refcount==1)
 * for zero-allocation in-place mutation.
 */

/* Cons: prepend an element to a list. elem is copied by value (elem_size bytes). */
SOMA_WARN_UNUSED SOMA_HOT
SomaListNode* soma_list_cons(const void* elem, SomaListNode* tail, uint16_t elem_size);

/* Head: pointer to the first element (caller must know the element type). */
SOMA_NONNULL(1) SOMA_HOT
void* soma_list_head(SomaListNode* list);

/* Tail: the list without its first element. Returns NULL if only one element. */
SOMA_NONNULL(1) SOMA_WARN_UNUSED SOMA_HOT
SomaListNode* soma_list_tail(SomaListNode* list);

/* DUP: increment refcount, return same pointer. */
SOMA_HOT
SomaListNode* soma_list_dup(SomaListNode* list);

/* ERA: decrement refcount, free chain when zero. */
SOMA_HOT
void soma_list_era(SomaListNode* list);

/* Build a list from a contiguous array of elements. */
SOMA_MALLOC SOMA_WARN_UNUSED
SomaListNode* soma_list_from_array(const void* data, uint32_t len, uint16_t elem_size);

/*
 * Closure operations
 */

SOMA_MALLOC SOMA_WARN_UNUSED
void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size);

SOMA_HOT SOMA_FLATTEN
void* soma_apply(void* closure, void* arg);

SOMA_NONNULL(1) void soma_closure_set_env(void* closure, uint16_t index, void* value);
SOMA_NONNULL(1) void* soma_closure_get_env(void* closure, uint16_t index);
SOMA_NONNULL(1) void* soma_closure_get_func(void* closure);

SOMA_HOT void soma_era_closure(void* closure);

SOMA_MALLOC SOMA_WARN_UNUSED
void* soma_clone_closure(void* closure, uint32_t label);

void* soma_clone_heap_value_for_dup(void* value, uint32_t label);

/*
 * SUP (Superposition) operations — Tier 3 lazy duplication
 */

SOMA_HOT SomaValue soma_dup_typed(uint32_t label, SomaValue value,
                                   SomaTypeDesc* type_desc);

SOMA_HOT SomaValue soma_proj0(SomaValue sup_val);
SOMA_HOT SomaValue soma_proj1(SomaValue sup_val);

/*
 * Memory Pool API
 *
 * Two size-class pools cover all fixed-size heap objects:
 *   pool_48  — small objects ≤48 bytes (SUPs, small closures, small strings)
 *   pool_112 — medium objects ≤112 bytes
 * Larger objects fall through to malloc.
 *
 * Each pool uses a bump-pointer fast path (bump_ptr/bump_limit) for
 * sequential allocation within a block, falling back to a LIFO free list
 * for recycled objects. This gives a single-comparison fast path for
 * fresh allocations.
 *
 * FUTURE: Region/arena allocator for batch deallocation of short-lived
 * objects (e.g., intermediate SUPs during reduction). Would supplement
 * the size-class pools with scope-based lifetime management.
 */

#define POOL_BLOCK_SIZE  (256 * 1024)  /* 256KB per block */
#define POOL_SIZE_48     48            /* Small objects + SUP nodes */
#define POOL_SIZE_112    112           /* Medium objects */

/* Memory pool block — linked list of bump-allocated slabs */
typedef struct SomaPoolBlock {
    struct SomaPoolBlock* next;
    uint32_t used;      /* bytes used in this block (max POOL_BLOCK_SIZE) */
    uint32_t _pad;
    char data[];        /* follows ptr+4+4 header; cache-line aligned via allocation */
} SomaPoolBlock;

/*
 * Pool with bump-pointer fast path.
 * bump_ptr/bump_limit avoid reloading block->used on every allocation.
 * Fields ordered so the hot triple (bump_ptr, bump_limit, free_list)
 * lives in a single cache line.
 */
typedef struct SomaPool {
    char*          bump_ptr;    /* next free byte in current block */
    char*          bump_limit;  /* end of current block's data region */
    void*          free_list;   /* LIFO free list of recycled objects */
    size_t         item_size;
    SomaPoolBlock* blocks;      /* linked list of allocated blocks */
} SomaPool;

/*
 * Per-thread pool set.
 * Each pool is cache-line aligned to prevent false sharing when one
 * pool is hot and the other is cold.
 */
typedef struct SomaPools {
    SomaPool pool_48  SOMA_ALIGNED(SOMA_CACHELINE);
    SomaPool pool_112 SOMA_ALIGNED(SOMA_CACHELINE);
} SomaPools;

extern SomaPools soma_pools;

void soma_pool_init(void);
void soma_pool_cleanup(void);

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_HOT
void* soma_pool_alloc_sup(void);

SOMA_HOT void soma_pool_free_sup(void* ptr);

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_ALLOC_SIZE(1) SOMA_HOT
void* soma_pool_alloc_raw(size_t byte_size);

SOMA_HOT void soma_pool_free_raw(void* ptr, size_t byte_size);

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_HOT
void* soma_alloc_view(void);

SOMA_HOT void soma_free_view(void* ptr);

/*
 * Pool statistics — opt-in via -DSOMA_POOL_STATS.
 */
#ifdef SOMA_POOL_STATS
typedef struct SomaPoolStats {
    _Atomic size_t sup_allocs;
    _Atomic size_t sup_frees;
    _Atomic size_t small_allocs;
    _Atomic size_t small_frees;
    _Atomic size_t medium_allocs;
    _Atomic size_t medium_frees;
    _Atomic size_t large_allocs;
    _Atomic size_t large_frees;
    _Atomic size_t blocks_allocated;
    _Atomic size_t bytes_allocated;
} SomaPoolStats;

extern SomaPoolStats soma_pool_stats;

#define SOMA_STAT_INC(field) atomic_fetch_add(&soma_pool_stats.field, 1)
#define SOMA_STAT_ADD(field, n) atomic_fetch_add(&soma_pool_stats.field, (n))
#else
#define SOMA_STAT_INC(field) ((void)0)
#define SOMA_STAT_ADD(field, n) ((void)0)
#endif


#endif /* SOMA_RUNTIME_H */
