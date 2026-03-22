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
 * Tagged Payload (count*8 bytes):
 *   [0]  i64  field[0]
 *   [8]  i64  field[1]  ...
 *   Pure data — the compiler-generated eraser knows field count/types.
 *
 * Closure (16 + env_size*8 bytes):
 *   [0]  u8   arity     (needed by soma_apply for PAP detection)
 *   [1]  u8   _pad[1]   (env_size low byte — used by soma_apply internally)
 *   [2]  u8   _pad[2]   (env_size high byte)
 *   [3-7] u8  _pad[3-7] (alignment)
 *   [8]  ptr  func_ptr  (function pointer)
 *   [16] i64  env[0]    ...
 *
 * String (8 + length + 1 bytes):
 *   [0]  i64  length    (byte count, excluding null terminator)
 *   [8]  char data[]    (inline, null-terminated)
 *
 * SUP (48 bytes, pool-allocated — keeps header for state machine):
 *   [0]  u8   tag        (SUP_TAG_*)
 *   [1]  u8[3] _pad      ('S','U','P')
 *   [4]  u32  label
 *   [8]  ptr  value
 *   [16] ptr  proj0
 *   [24] ptr  proj1
 *   [32] ptr  type_desc
 *
 * Flat Array View (32 bytes — keeps header for tag dispatch):
 *   [0]  u8   tag         (NODE_FLAT_ARRAY_VIEW = 5)
 *   [1]  u8[3] _pad
 *   [4]  u32  _reserved
 *   [8]  i64  length
 *   [16] ptr  data
 *   [24] ptr  backing
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
 * Low 3 bits of pointers for type tags (assuming 8-byte alignment).
 *
 * Pointer format (64-bit):
 *   [63:3] payload  [2:0] tag
 *
 * Tag values:
 *   000 = Heap pointer (closure, etc.) - must be 8-byte aligned
 *   001 = Small integer (63-bit signed, shifted right by 3)
 *   010 = Boolean/Unit (payload: 0=false, 1=true, 2=unit)
 *   011 = Character (payload: Unicode codepoint)
 */

#define TAG_BITS        3
#define TAG_MASK        0x7ULL
#define PAYLOAD_SHIFT   3

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

/* Create/extract small integer */
#define SOMA_INT(n)          ((((SomaValue)(int64_t)(n)) << PAYLOAD_SHIFT) | TAG_INT)
#define SOMA_TO_INT(v)       ((int64_t)(v) >> PAYLOAD_SHIFT)

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
 * Closure structure (env follows at offset 16)
 *
 * _pad[0] = NODE_CLOSURE sentinel for runtime identification by soma_era_free.
 * _pad[1..2] = env_size as little-endian u16 (needed by soma_apply for PAP
 *   creation and by soma_era_closure for dynamic env traversal).
 */
typedef struct SomaClosure {
    uint8_t  arity;       /* remaining args (needed by soma_apply) */
    uint8_t  _pad[7];     /* [0]=NODE_CLOSURE, [1..2]=env_size LE16, [3..6]=reserved */
    void*    func_ptr;    /* function pointer */
    /* SomaValue env[] follows at offset 16 */
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
 * String structure (length + inline data, no header overhead)
 *
 * The MSB of `length` is a static sentinel: static string globals
 * emitted by the compiler have bit 63 set, preventing soma_era_string
 * from freeing read-only memory.  All length readers use
 * soma_string_len() which masks the sentinel bit.
 */
#define SOMA_STRING_STATIC_BIT ((int64_t)1 << 63)

typedef struct SomaString {
    int64_t  length;    /* byte count; bit 63 = static sentinel */
    char     data[];    /* flexible array member: string data inline */
} SomaString;

static inline int64_t soma_string_len(const SomaString* s) {
    return s->length & ~SOMA_STRING_STATIC_BIT;
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

/* Layout guards — catch struct packing surprises across compilers */
_Static_assert(sizeof(SomaClosure)      == 16, "SomaClosure must be 16 bytes");
_Static_assert(sizeof(SomaSup)          == 48
            || sizeof(SomaSup)          == 40, "SomaSup must fit pool_48");
_Static_assert(sizeof(SomaFlatArrayView) == 32, "View must fit pool_48");
_Static_assert(sizeof(SomaFlatArray)    == 16, "FlatArray header must be 16 bytes");


/*
 * Core runtime functions
 */

SOMA_HOT void soma_era_free(void* value);

SOMA_NORETURN SOMA_COLD void soma_panic(const char* msg);

/*
 * String operations
 */

SOMA_NONNULL(1) char* soma_to_cstring(SomaString* str);

SOMA_MALLOC SOMA_WARN_UNUSED
SomaString* soma_from_cstring(const char* cstr);

uint64_t soma_cstring_len(const char* cstr);

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_HOT
SomaString* soma_strcat(SomaString* a, SomaString* b);

SOMA_MALLOC SOMA_WARN_UNUSED
SomaString* soma_int_to_string(int32_t val);

void soma_era_string(void* value);

/*
 * Flat array view operations
 */

SOMA_MALLOC SOMA_WARN_UNUSED SOMA_HOT
void* soma_clone_flat_array_view(SomaFlatArrayView* src);

/*
 * Closure operations
 */

SOMA_MALLOC SOMA_WARN_UNUSED
void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size);

SOMA_HOT SOMA_FLATTEN
void* soma_apply(void* closure, void* arg);

SOMA_NONNULL(1) void soma_closure_set_env(void* closure, uint16_t index, SomaValue value);
SOMA_NONNULL(1) SomaValue soma_closure_get_env(void* closure, uint16_t index);
SOMA_NONNULL(1) void* soma_closure_get_func(void* closure);

SOMA_HOT void soma_era_closure(void* closure);

SOMA_MALLOC SOMA_WARN_UNUSED
void* soma_clone_closure(void* closure, uint32_t label);

SomaValue soma_clone_heap_value_for_dup(SomaValue value, uint32_t label);

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
    char data[];        /* 16-byte aligned (follows 8+4+4 header) */
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
