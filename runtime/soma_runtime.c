#include "soma_runtime.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifdef _WIN32
#include <windows.h>
#endif

#ifndef _WIN32
#include <unistd.h>
#endif

/*
 * Portable aligned allocation.
 * Pool blocks are cache-line aligned (64 bytes) to prevent false sharing
 * and enable aligned SIMD loads within the data region.
 */
static inline void* soma_aligned_alloc(size_t alignment, size_t size) {
#if defined(_WIN32)
    return _aligned_malloc(size, alignment);
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__APPLE__)
    size = (size + alignment - 1) & ~(alignment - 1);
    return aligned_alloc(alignment, size);
#else
    void* ptr = NULL;
    posix_memalign(&ptr, alignment, size);
    return ptr;
#endif
}

static inline void soma_aligned_free(void* ptr) {
#if defined(_WIN32)
    _aligned_free(ptr);
#else
    free(ptr);
#endif
}


/* Global memory pools */
SomaPools soma_pools;

#ifdef SOMA_POOL_STATS
SomaPoolStats soma_pool_stats;
#endif


/*
 * ============================================================================
 * Size-Class Pool Allocator (TLS) with Bump-Pointer Fast Path
 * ============================================================================
 */

/* Thread-local pool storage */
__thread SomaPools* tls_pools = NULL;

/* Allocate a new block for a pool — cold path, called rarely */
SOMA_COLD SOMA_NOINLINE
static SomaPoolBlock* pool_alloc_block(void) {
    /* Cache-line aligned so data[] starts at a predictable boundary */
    SomaPoolBlock* block = (SomaPoolBlock*)soma_aligned_alloc(
        SOMA_CACHELINE, sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE
    );
    if (SOMA_LIKELY(block != NULL)) {
        block->next = NULL;
        block->used = 0;
        SOMA_STAT_INC(blocks_allocated);
        SOMA_STAT_ADD(bytes_allocated, sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE);
    }
    return block;
}

static void pool_init(SomaPool* pool, size_t item_size) {
    SomaPoolBlock* block = pool_alloc_block();
    pool->blocks = block;
    pool->item_size = item_size;
    pool->free_list = NULL;
    if (SOMA_LIKELY(block != NULL)) {
        pool->bump_ptr = block->data;
        pool->bump_limit = block->data + POOL_BLOCK_SIZE;
    } else {
        pool->bump_ptr = NULL;
        pool->bump_limit = NULL;
    }
}

static void pool_cleanup(SomaPool* pool) {
    SomaPoolBlock* block = pool->blocks;
    while (block) {
        SomaPoolBlock* next = block->next;
        soma_aligned_free(block);
        block = next;
    }
    pool->blocks = NULL;
    pool->free_list = NULL;
    pool->bump_ptr = NULL;
    pool->bump_limit = NULL;
}

/*
 * Allocate from a pool.
 * Fast path: bump pointer (single comparison).
 * Medium path: free list (LIFO, cache-warm).
 * Slow path: allocate new block.
 */
SOMA_HOT
static inline void* pool_alloc(SomaPool* pool) {
    /* Bump-pointer fast path — single comparison */
    const size_t item_size = pool->item_size;
    char* ptr = pool->bump_ptr;
    char* new_ptr = ptr + item_size;
    if (SOMA_LIKELY(new_ptr <= pool->bump_limit)) {
        pool->bump_ptr = new_ptr;
        return SOMA_ASSUME_ALIGNED(ptr, 16);
    }

    /* Free list — recycle previously freed objects */
    if (pool->free_list != NULL) {
        void* result = pool->free_list;
        pool->free_list = *(void**)result;
        if (pool->free_list != NULL) {
            SOMA_PREFETCH(pool->free_list);
        }
        return result;
    }

    /* Slow path: need new block */
    SomaPoolBlock* new_block = pool_alloc_block();
    if (SOMA_UNLIKELY(!new_block)) {
        return NULL;
    }
    new_block->next = pool->blocks;
    pool->blocks = new_block;

    pool->bump_ptr = new_block->data + item_size;
    pool->bump_limit = new_block->data + POOL_BLOCK_SIZE;
    return SOMA_ASSUME_ALIGNED(new_block->data, 16);
}

/* Return to pool's free list (LIFO — recently freed = cache-warm on reuse) */
SOMA_HOT
static inline void pool_free(SomaPool* pool, void* ptr) {
    *(void**)ptr = pool->free_list;
    pool->free_list = ptr;
}

static void tls_pool_init(void) {
    if (SOMA_LIKELY(tls_pools != NULL)) return;

    tls_pools = (SomaPools*)soma_aligned_alloc(SOMA_CACHELINE, sizeof(SomaPools));
    if (SOMA_LIKELY(tls_pools != NULL)) {
        pool_init(&tls_pools->pool_48, POOL_SIZE_48);
        pool_init(&tls_pools->pool_112, POOL_SIZE_112);
    }
}

static void tls_pool_cleanup(void) {
    if (SOMA_UNLIKELY(tls_pools == NULL)) return;

    pool_cleanup(&tls_pools->pool_48);
    pool_cleanup(&tls_pools->pool_112);
    soma_aligned_free(tls_pools);
    tls_pools = NULL;
}

static inline SomaPools* get_pools(void) {
    return tls_pools;
}

void soma_pool_init(void) {
#ifdef SOMA_POOL_STATS
    memset(&soma_pool_stats, 0, sizeof(soma_pool_stats));
#endif
    tls_pool_init();
}

void soma_pool_cleanup(void) {
    tls_pool_cleanup();
}

/*
 * ============================================================================
 * Generic Size-Class Pool Allocation
 * ============================================================================
 */

SOMA_HOT
void* soma_pool_alloc_raw(size_t byte_size) {
    SomaPools* pools = get_pools();

    if (SOMA_LIKELY(byte_size <= POOL_SIZE_48)) {
        SOMA_STAT_INC(small_allocs);
        return pool_alloc(&pools->pool_48);
    }
    if (SOMA_LIKELY(byte_size <= POOL_SIZE_112)) {
        SOMA_STAT_INC(medium_allocs);
        return pool_alloc(&pools->pool_112);
    }

    SOMA_STAT_INC(large_allocs);
    return malloc(byte_size);
}

SOMA_HOT
void soma_pool_free_raw(void* ptr, size_t byte_size) {
    SomaPools* pools = get_pools();

    if (SOMA_LIKELY(byte_size <= POOL_SIZE_48)) {
        SOMA_STAT_INC(small_frees);
        pool_free(&pools->pool_48, ptr);
    } else if (SOMA_LIKELY(byte_size <= POOL_SIZE_112)) {
        SOMA_STAT_INC(medium_frees);
        pool_free(&pools->pool_112, ptr);
    } else {
        SOMA_STAT_INC(large_frees);
        free(ptr);
    }
}

/*
 * ============================================================================
 * SUP Pool Operations
 * ============================================================================
 */

SOMA_HOT
void* soma_pool_alloc_sup(void) {
    SOMA_STAT_INC(sup_allocs);
    SomaPools* pools = get_pools();
    return pool_alloc(&pools->pool_48);
}

SOMA_HOT
void soma_pool_free_sup(void* ptr) {
    SOMA_STAT_INC(sup_frees);
    SomaPools* pools = get_pools();
    pool_free(&pools->pool_48, ptr);
}

/*
 * ============================================================================
 * Flat Array View Pool
 * ============================================================================
 */

SOMA_HOT
void* soma_alloc_view(void) {
    SomaPools* pools = get_pools();
    SOMA_STAT_INC(small_allocs);
    return pool_alloc(&pools->pool_48);
}

SOMA_HOT
void soma_free_view(void* ptr) {
    SomaPools* pools = get_pools();
    SOMA_STAT_INC(small_frees);
    pool_free(&pools->pool_48, ptr);
}

/*
 * ============================================================================
 * Flat Array View Clone
 * ============================================================================
 */

SOMA_HOT
void* soma_clone_flat_array_view(SomaFlatArrayView* restrict src) {
    if (SOMA_UNLIKELY(src == NULL)) return NULL;

    SomaFlatArray* srcBacking = (SomaFlatArray*)src->backing;
    SomaFlatArray* newBacking = NULL;
    void* newData = NULL;

    if (srcBacking != NULL) {
        size_t backingTotal = sizeof(SomaFlatArray) +
            (size_t)srcBacking->length * (size_t)srcBacking->elem_size;
        newBacking = (SomaFlatArray*)soma_pool_alloc_raw(backingTotal);
        if (SOMA_UNLIKELY(newBacking == NULL)) {
            soma_panic("soma_clone_flat_array_view: out of memory");
        }
        memcpy(newBacking, srcBacking, backingTotal);
        newBacking->_reserved = 0;

        ptrdiff_t offset = (char*)src->data - (char*)(srcBacking + 1);
        newData = (char*)(newBacking + 1) + offset;
    }

    SomaFlatArrayView* restrict dst = (SomaFlatArrayView*)soma_alloc_view();
    if (SOMA_UNLIKELY(dst == NULL)) {
        soma_panic("soma_clone_flat_array_view: out of memory");
    }
    dst->tag = NODE_FLAT_ARRAY_VIEW;
    dst->length = src->length;
    dst->data = newData;
    dst->backing = newBacking;
    return dst;
}

/*
 * ============================================================================
 * Array-Backed List Operations
 *
 * A SomaList is a value type: { data, len, cap, offset }.
 * `data` points to a contiguous buffer of `cap` element slots.
 * Live elements occupy data[offset .. offset+len).
 *
 * Ownership: each SomaList exclusively owns its `data` buffer.
 * No reference counting. DUP = memcpy of live region into fresh buffer.
 * ERA = free(data).
 *
 * Cons strategy: elements are prepended by writing at data[offset-1].
 * Buffers are allocated with geometric slack *before* the first element,
 * so repeated cons is O(1) amortized. When slack is exhausted, the buffer
 * is grown and existing elements are copied to the right half, leaving
 * the left half as prepend room.
 *
 * Tail strategy: advance offset, decrement len. No allocation, no copy.
 * The dropped head element becomes dead space (reclaimed when the list
 * is freed or DUP'd — DUP only copies the live region).
 * ============================================================================
 */

/*
 * Growth policy: minimum capacity and geometric factor.
 *
 * SOMA_LIST_MIN_CAP: smallest buffer we'll allocate. Sized for one cache
 * line of i32 elements (16 elements × 4 bytes = 64 bytes). For larger
 * element types, the minimum is clamped to at least 4 slots.
 *
 * Growth factor: 2× (standard doubling). On reallocation, existing elements
 * are placed in the RIGHT half of the new buffer, so the left half is
 * available for future cons operations.
 */
#define SOMA_LIST_MIN_CAP(elem_size) \
    ((uint32_t)(SOMA_CACHELINE / (elem_size) < 4 ? 4 : SOMA_CACHELINE / (elem_size)))

SOMA_HOT
SomaList soma_list_cons(const void* elem, SomaList tail, uint16_t elem_size) {
    /* Fast path: tail has slack before the live region (offset > 0). */
    if (SOMA_LIKELY(tail.offset > 0)) {
        tail.offset--;
        tail.len++;
        memcpy((char*)tail.data + (size_t)tail.offset * elem_size, elem, elem_size);
        return tail;
    }

    /* Slow path: grow buffer geometrically, place elements at right end. */
    uint32_t old_len = tail.len;
    uint32_t min_cap = SOMA_LIST_MIN_CAP(elem_size);
    uint32_t new_cap = old_len * 2;
    if (new_cap < min_cap) new_cap = min_cap;
    if (new_cap <= old_len) new_cap = old_len + 1;

    void* new_data = malloc((size_t)new_cap * elem_size);
    if (SOMA_UNLIKELY(new_data == NULL)) soma_panic("soma_list_cons: out of memory");

    uint32_t new_offset = new_cap - old_len;
    if (old_len > 0) {
        memcpy((char*)new_data + (size_t)new_offset * elem_size,
               (char*)tail.data + (size_t)tail.offset * elem_size,
               (size_t)old_len * elem_size);
    }
    free(tail.data);

    new_offset--;
    memcpy((char*)new_data + (size_t)new_offset * elem_size, elem, elem_size);
    return (SomaList){ new_data, old_len + 1, new_offset };
}

SOMA_HOT
void* soma_list_head(SomaList list, uint16_t elem_size) {
    return (char*)list.data + (size_t)list.offset * elem_size;
}

SOMA_HOT
SomaList soma_list_tail(SomaList list, uint16_t elem_size) {
    (void)elem_size;
    return (SomaList){ list.data, list.len - 1, list.offset + 1 };
}

SOMA_HOT
SomaList soma_list_dup(SomaList list, uint16_t elem_size) {
    if (list.len == 0) return SOMA_LIST_NIL;
    size_t live_bytes = (size_t)list.len * elem_size;
    void* new_data = malloc(live_bytes);
    if (SOMA_UNLIKELY(new_data == NULL)) soma_panic("soma_list_dup: out of memory");
    memcpy(new_data, (char*)list.data + (size_t)list.offset * elem_size, live_bytes);
    return (SomaList){ new_data, list.len, 0 };
}

SOMA_HOT
void soma_list_era(SomaList list) {
    free(list.data);
}

SomaList soma_list_from_array(const void* data, uint32_t len, uint16_t elem_size) {
    if (len == 0) return SOMA_LIST_NIL;
    uint32_t min_cap = SOMA_LIST_MIN_CAP(elem_size);
    uint32_t cap = len < min_cap ? min_cap : len;
    void* buf = malloc((size_t)cap * elem_size);
    if (SOMA_UNLIKELY(buf == NULL)) soma_panic("soma_list_from_array: out of memory");
    uint32_t offset = cap - len;
    memcpy((char*)buf + (size_t)offset * elem_size, data, (size_t)len * elem_size);
    return (SomaList){ buf, len, offset };
}

/*
 * ============================================================================
 * Boxed List for SUP Integration
 *
 * SUP nodes store values as void* pointers. SomaList is a 16-byte value type
 * that doesn't fit in a pointer. When a list enters a SUP (via DUP), it's
 * "boxed" — heap-allocated as a SomaBoxedList that holds the struct fields
 * plus the elem_size needed for cloning.
 *
 * The boxed representation is:
 *   { void* data, uint32_t len, uint32_t offset, uint16_t elem_size }
 *
 * Clone: deep-copies the backing buffer (soma_list_dup semantics).
 * Erase: frees the backing buffer, then frees the box itself.
 * ============================================================================
 */

typedef struct SomaBoxedList {
    void*    data;
    uint32_t len;
    uint32_t offset;
    uint16_t elem_size;
} SomaBoxedList;

/* Box a SomaList value onto the heap for SUP storage. */
static inline SomaBoxedList* soma_list_box(SomaList list, uint16_t elem_size) {
    SomaBoxedList* box = (SomaBoxedList*)malloc(sizeof(SomaBoxedList));
    if (SOMA_UNLIKELY(box == NULL)) soma_panic("soma_list_box: out of memory");
    box->data = list.data;
    box->len = list.len;
    box->offset = list.offset;
    box->elem_size = elem_size;
    return box;
}

/* Unbox: read the SomaList fields from a boxed representation (internal). */
static inline SomaList soma_list_unbox_internal(SomaBoxedList* box) {
    return (SomaList){ box->data, box->len, box->offset };
}

/* Clone function for SomaTypeDesc — deep-copies the backing buffer. */
void* soma_clone_boxed_list(void* value, uint32_t label) {
    (void)label;
    SomaBoxedList* src = (SomaBoxedList*)value;
    SomaList dup = soma_list_dup(soma_list_unbox_internal(src), src->elem_size);
    return (void*)soma_list_box(dup, src->elem_size);
}

/* Erase function for SomaTypeDesc — frees buffer and box. */
void soma_era_boxed_list(void* value) {
    SomaBoxedList* box = (SomaBoxedList*)value;
    free(box->data);
    free(box);
}

/* TypeDesc for boxed lists — static global, initialized on first use. */
static SomaTypeDesc soma_boxed_list_typedesc = {
    .clone_fn = soma_clone_boxed_list,
    .erase_fn = soma_era_boxed_list,
};

/* Box a SomaList for SUP storage. Called by compiler-generated DUP code. */
void* soma_list_box_for_sup(SomaList list, uint16_t elem_size) {
    return (void*)soma_list_box(list, elem_size);
}

/* Create a SUP node for a boxed list. Combines boxing + soma_dup_typed. */
SomaValue soma_dup_typed_list(uint32_t label, void* boxed_list) {
    return soma_dup_typed(label, (SomaValue)boxed_list, &soma_boxed_list_typedesc);
}

/* Unbox a SomaList from a boxed pointer. Called after SUP projection. */
SomaList soma_list_unbox(void* boxed) {
    SomaBoxedList* box = (SomaBoxedList*)boxed;
    return (SomaList){ box->data, box->len, box->offset };
}

/*
 * ============================================================================
 * Generic Heap Value Clone (SUP/view/array only)
 * ============================================================================
 */

void* soma_clone_heap_value_for_dup(void* value, uint32_t label) {
    if (value == NULL) return NULL;

    uint8_t tag = *(uint8_t*)value;

    if (IS_SUP(tag)) {
        return (void*)soma_dup_typed(label, (SomaValue)value, NULL);
    }
    if (tag == NODE_FLAT_ARRAY_VIEW) {
        return soma_clone_flat_array_view((SomaFlatArrayView*)value);
    }
    if (tag == NODE_FLAT_ARRAY) {
        SomaFlatArray* arr = (SomaFlatArray*)value;
        size_t total = sizeof(SomaFlatArray) +
            (size_t)arr->length * (size_t)arr->elem_size;
        SomaFlatArray* copy = (SomaFlatArray*)malloc(total);
        if (SOMA_UNLIKELY(copy == NULL)) {
            soma_panic("soma_clone_heap_value_for_dup: out of memory");
        }
        memcpy(copy, arr, total);
        return copy;
    }

    if (((uint8_t*)value)[1] == NODE_CLOSURE) {
        return soma_clone_closure(value, label);
    }

    soma_panic("soma_clone_heap_value_for_dup: unrecognized heap object (missing typed cloner)");
#if defined(__GNUC__) || defined(__clang__)
    __builtin_unreachable();
#else
    return value;
#endif
}

/*
 * ============================================================================
 * SUP Operations
 * ============================================================================
 */

SOMA_HOT
SomaValue soma_dup_typed(uint32_t label, SomaValue value,
                     SomaTypeDesc* type_desc) {
    SomaSup* sup = (SomaSup*)soma_pool_alloc_sup();

    /*
     * H: Pack tag + _pad[0..2] into a single 32-bit store.
     * Little-endian: [SUP_TAG_FRESH, 'S', 'U', 'P']
     * One store-queue entry instead of four byte stores.
     */
    uint32_t header = SOMA_SUP_HEADER_FRESH;
    memcpy(&sup->tag, &header, sizeof(uint32_t));

    sup->label = label;
    sup->value = (void*)value;
    sup->type_desc = type_desc;
    return SOMA_PTR(sup);
}

SOMA_HOT
static inline int is_heap_sup(SomaValue value) {
    SomaValue sv = (SomaValue)(uintptr_t)value;
    if (!SOMA_IS_PTR(sv) || sv == 0) return 0;
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sv);
    if (!IS_SUP(sup->tag)) return 0;
    uint32_t pad_val;
    memcpy(&pad_val, sup->_pad, sizeof(uint32_t));
    return (pad_val & 0x00FFFFFFu) == SOMA_SUP_MAGIC_U32;
}

SOMA_HOT
static inline SomaValue soma_proj_impl(SomaValue sup_val, int proj_idx) {
    if (!SOMA_IS_PTR(sup_val) || sup_val == 0) return sup_val;

    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    uint8_t tag = sup->tag;

    const uint8_t my_proj_tag    = (proj_idx == 0) ? SUP_TAG_PROJ0 : SUP_TAG_PROJ1;
    const uint8_t other_proj_tag = (proj_idx == 0) ? SUP_TAG_PROJ1 : SUP_TAG_PROJ0;
    void** my_slot = (proj_idx == 0) ? &sup->proj0 : &sup->proj1;

    if (SOMA_LIKELY(tag == SUP_TAG_FRESH)) {
        sup->tag = my_proj_tag;
        SomaValue value = (SomaValue)sup->value;

        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                *my_slot = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        *my_slot = (void*)value;
        return value;
    }

    if (tag == other_proj_tag) {
        sup->tag = SUP_TAG_BOTH;
        SomaValue value = (SomaValue)sup->value;

        if (!SOMA_IS_PTR(value) || value == 0) {
            *my_slot = (void*)value;
            return value;
        }

        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                *my_slot = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        SomaValue cloned;
        if (sup->type_desc != NULL) {
            cloned = (SomaValue)sup->type_desc->clone_fn((void*)value, sup->label);
        } else {
            cloned = (SomaValue)soma_clone_heap_value_for_dup((void*)value, sup->label);
        }
        *my_slot = (void*)cloned;
        return cloned;
    }

    return (SomaValue)*my_slot;
}

SOMA_HOT
SomaValue soma_proj0(SomaValue sup_val) {
    return soma_proj_impl(sup_val, 0);
}

SOMA_HOT
SomaValue soma_proj1(SomaValue sup_val) {
    return soma_proj_impl(sup_val, 1);
}

/*
 * ============================================================================
 * Closure Operations
 * ============================================================================
 */

void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size) {
    size_t byte_size = sizeof(SomaClosure) + env_size * sizeof(void*);
    SomaClosure* closure = (SomaClosure*)soma_pool_alloc_raw(byte_size);

    uint32_t packed = (uint32_t)arity
                    | ((uint32_t)NODE_CLOSURE << 8)
                    | ((uint32_t)(env_size & 0xFF) << 16)
                    | ((uint32_t)((env_size >> 8) & 0xFF) << 24);
    memcpy(&closure->arity, &packed, sizeof(uint32_t));
    closure->func_ptr = func_ptr;

    return closure;
}

SOMA_NONNULL(1)
void soma_closure_set_env(void* closure_ptr, uint16_t index, void* value) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    void** env = (void**)(closure + 1);
    env[index] = value;
}

SOMA_NONNULL(1)
void* soma_closure_get_env(void* closure_ptr, uint16_t index) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    void** env = (void**)(closure + 1);
    return env[index];
}

SOMA_NONNULL(1)
void* soma_closure_get_func(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    return closure->func_ptr;
}

SOMA_HOT
void soma_era_closure(void* closure_ptr) {
    if (SOMA_UNLIKELY(closure_ptr == NULL)) return;
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint16_t env_size = CLOSURE_ENV_SIZE(closure);
    void** env = (void**)(closure + 1);
    for (uint16_t i = 0; i < env_size; i++) {
        SomaValue sv = (SomaValue)(uintptr_t)env[i];
        if (SOMA_IS_PTR(sv) && sv != 0) {
            soma_era_free(SOMA_TO_PTR(sv));
        }
    }
    size_t byte_size = sizeof(SomaClosure) + env_size * sizeof(void*);
    SomaPools* pools = get_pools();
    if (SOMA_LIKELY(byte_size <= POOL_SIZE_48)) {
        SOMA_STAT_INC(small_frees);
        pool_free(&pools->pool_48, closure_ptr);
    } else if (byte_size <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_frees);
        pool_free(&pools->pool_112, closure_ptr);
    } else {
        SOMA_STAT_INC(large_frees);
        free(closure_ptr);
    }
}

#define SOMA_MAX_CALL_ARGS 16

static void* soma_call_with_args(void* (*fn)(), void** args, unsigned nargs) {
    if (SOMA_LIKELY(nargs == 1))
        return ((void*(*)(void*))fn)(args[0]);
    if (SOMA_LIKELY(nargs == 2))
        return ((void*(*)(void*,void*))fn)(args[0], args[1]);
    if (SOMA_LIKELY(nargs == 3))
        return ((void*(*)(void*,void*,void*))fn)(args[0], args[1], args[2]);

    switch (nargs) {
        case 0:  return fn();
        case 4:  return ((void*(*)(void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3]);
        case 5:  return ((void*(*)(void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4]);
        case 6:  return ((void*(*)(void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6]);
        case 8:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7]);
        case 9:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8]);
        case 10: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9]);
        case 11: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10]);
        case 12: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11]);
        case 13: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12]);
        case 14: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13]);
        case 15: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13], args[14]);
        case 16: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13], args[14], args[15]);
        default:
            soma_panic("soma_call_with_args: too many arguments (max 16)");
#if defined(__GNUC__) || defined(__clang__)
            __builtin_unreachable();
#else
            return NULL;
#endif
    }
}

/*
 * Apply one argument to a closure (eval/apply, Marlow & Peyton Jones 2004).
 *
 * SOMA_FLATTEN force-inlines all callees (pool_alloc, soma_call_with_args,
 * CLOSURE_ENV_SIZE) into one large optimized function body — the single
 * hottest path in any eval/apply functional language runtime.
 */
SOMA_HOT SOMA_FLATTEN
void* soma_apply(void* closure_ptr, void* arg) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint8_t arity = closure->arity;
    void* (*fn)() = (void* (*)())closure->func_ptr;
    void** env = (void**)(closure + 1);
    uint16_t env_size = CLOSURE_ENV_SIZE(closure);

    while (SOMA_UNLIKELY(arity == 0)) {
        void* args[SOMA_MAX_CALL_ARGS];
        unsigned n = (env_size < SOMA_MAX_CALL_ARGS) ? env_size : SOMA_MAX_CALL_ARGS;
        for (unsigned i = 0; i < n; i++)
            args[i] = env[i];
        void* result = soma_call_with_args(fn, args, n);

        closure = (SomaClosure*)result;
        arity = closure->arity;
        fn = (void* (*)())closure->func_ptr;
        env = (void**)(closure + 1);
        env_size = CLOSURE_ENV_SIZE(closure);
    }

    if (SOMA_LIKELY(arity == 1)) {
        switch (env_size) {
        case 0:
            return ((void*(*)(void*))fn)(arg);
        case 1:
            return ((void*(*)(void*,void*))fn)(env[0], arg);
        case 2:
            return ((void*(*)(void*,void*,void*))fn)(
                env[0], env[1], arg);
        case 3:
            return ((void*(*)(void*,void*,void*,void*))fn)(
                env[0], env[1], env[2], arg);
        default: {
            void* args[SOMA_MAX_CALL_ARGS];
            uint16_t n = 0;
            for (uint16_t i = 0; i < env_size && n < SOMA_MAX_CALL_ARGS - 1; i++)
                args[n++] = env[i];
            args[n++] = arg;
            return soma_call_with_args(fn, args, n);
        }
        }
    }

    /* PAP */
    uint16_t new_env_size = env_size + 1;
    size_t pap_bytes = sizeof(SomaClosure) + new_env_size * sizeof(void*);
    SomaClosure* pap = (SomaClosure*)soma_pool_alloc_raw(pap_bytes);

    uint32_t packed = (uint32_t)(arity - 1)
                    | ((uint32_t)NODE_CLOSURE << 8)
                    | ((uint32_t)(new_env_size & 0xFF) << 16)
                    | ((uint32_t)((new_env_size >> 8) & 0xFF) << 24);
    memcpy(&pap->arity, &packed, sizeof(uint32_t));
    pap->func_ptr = closure->func_ptr;

    void** pap_env = (void**)(pap + 1);
    if (env_size > 0) {
        memcpy(pap_env, env, env_size * sizeof(void*));
    }
    pap_env[env_size] = arg;

    return pap;
}

/*
 * N: Pre-scan env for heap pointers. If all env slots are value types
 * (ints, bools, chars), bulk-copy the closure without deep cloning.
 */
void* soma_clone_closure(void* closure_ptr, uint32_t label) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint16_t env_size = CLOSURE_ENV_SIZE(closure);

    size_t byte_size = sizeof(SomaClosure) + env_size * sizeof(void*);
    void* new_closure = soma_pool_alloc_raw(byte_size);

    if (env_size == 0) {
        memcpy(new_closure, closure, sizeof(SomaClosure));
        return new_closure;
    }

    /* Pre-scan: any env slot that's a heap pointer? */
    void** src_env = (void**)(closure + 1);
    int has_heap_ptrs = 0;
    for (uint16_t i = 0; i < env_size; i++) {
        SomaValue sv = (SomaValue)(uintptr_t)src_env[i];
        if (SOMA_IS_PTR(sv) && sv != 0) {
            has_heap_ptrs = 1;
            break;
        }
    }

    if (!has_heap_ptrs) {
        /* All env slots are value types — bulk copy entire closure */
        memcpy(new_closure, closure, byte_size);
        return new_closure;
    }

    /* Deep clone each env slot */
    memcpy(new_closure, closure, sizeof(SomaClosure));
    void** dst_env = (void**)((SomaClosure*)new_closure + 1);

    for (uint16_t i = 0; i < env_size; i++) {
        dst_env[i] = soma_clone_heap_value_for_dup(src_env[i], label);
    }

    return new_closure;
}

/*
 * ============================================================================
 * String Operations
 * ============================================================================
 */

SOMA_NONNULL(1)
/* soma_to_cstring is now inline in the header (just returns str.data) */

SomaString soma_from_cstring(const char* cstr) {
    if (SOMA_UNLIKELY(cstr == NULL))
        return (SomaString){ .data = NULL, .len = 0 };
    size_t len = strlen(cstr);
    char* buf = (char*)soma_pool_alloc_raw(len + 1);
    if (SOMA_UNLIKELY(buf == NULL)) soma_panic("soma_from_cstring: out of memory");
    memcpy(buf, cstr, len + 1);
    return (SomaString){ .data = buf, .len = (int64_t)len };
}

SOMA_HOT
SomaString soma_strcat(SomaString a, SomaString b) {
    size_t len_a = (size_t)soma_string_len(a);
    size_t len_b = (size_t)soma_string_len(b);
    size_t total_len = len_a + len_b;
    char* buf = (char*)soma_pool_alloc_raw(total_len + 1);
    if (SOMA_UNLIKELY(buf == NULL)) soma_panic("soma_strcat: out of memory");
    memcpy(buf, a.data, len_a);
    memcpy(buf + len_a, b.data, len_b);
    buf[total_len] = '\0';
    return (SomaString){ .data = buf, .len = (int64_t)total_len };
}

SomaString soma_int_to_string(int32_t val) {
    char tmp[12];
    char* p = tmp + sizeof(tmp);
    *--p = '\0';
    uint32_t uval;
    int negative = 0;
    if (val < 0) { negative = 1; uval = (uint32_t)(-(int64_t)val); }
    else { uval = (uint32_t)val; }
    do { *--p = '0' + (char)(uval % 10); uval /= 10; } while (uval > 0);
    if (negative) *--p = '-';
    int len = (int)(tmp + sizeof(tmp) - 1 - p);
    char* buf = (char*)soma_pool_alloc_raw(len + 1);
    if (SOMA_UNLIKELY(buf == NULL)) soma_panic("soma_int_to_string: out of memory");
    memcpy(buf, p, len + 1);
    return (SomaString){ .data = buf, .len = (int64_t)len };
}

void soma_era_string(SomaString str) {
    if (SOMA_UNLIKELY(str.data == NULL)) return;
    if (str.len < 0) return;  /* static string — don't free */
    soma_pool_free_raw(str.data, (size_t)str.len + 1);
}

/*
 * ============================================================================
 * soma_era_free — Free SUPs, flat arrays, flat array views, and closures
 * ============================================================================
 */

#define ERA_STACK_INLINE 64

SOMA_HOT
void soma_era_free(void* value) {
    if (SOMA_UNLIKELY(value == NULL)) return;

    void*  stack_buf[ERA_STACK_INLINE];
    void** stack = stack_buf;
    int    sp    = 0;
    int    cap   = ERA_STACK_INLINE;

    stack[sp++] = value;

    SomaPools* pools = get_pools();

    while (sp > 0) {
        void* cur = stack[--sp];
        if (SOMA_UNLIKELY(cur == NULL)) continue;

        uint8_t tag = *(uint8_t*)cur;

        #define ERA_ENSURE(n) do {                                     \
            if (SOMA_UNLIKELY(sp + (n) > cap)) {                       \
                int new_cap = cap * 2;                                 \
                while (new_cap < sp + (n)) new_cap *= 2;              \
                if (stack == stack_buf) {                               \
                    stack = (void**)malloc(new_cap * sizeof(void*));    \
                    memcpy(stack, stack_buf, sp * sizeof(void*));       \
                } else {                                               \
                    stack = (void**)realloc(stack, new_cap * sizeof(void*)); \
                }                                                      \
                cap = new_cap;                                         \
            }                                                          \
        } while (0)

        if (tag == NODE_FLAT_ARRAY_VIEW) {
            SomaFlatArrayView* view = (SomaFlatArrayView*)cur;
            if (view->backing != NULL) {
                SomaFlatArray* backing = (SomaFlatArray*)view->backing;
                size_t backing_size = sizeof(SomaFlatArray) +
                    (size_t)backing->length * (size_t)backing->elem_size;
                soma_pool_free_raw(view->backing, backing_size);
            }
            SOMA_STAT_INC(small_frees);
            pool_free(&pools->pool_48, cur);

        } else if (tag == NODE_FLAT_ARRAY) {
            free(cur);

        } else if (IS_SUP(tag)) {
            SomaSup* sup = (SomaSup*)cur;

            SomaValue v = (SomaValue)sup->value;
            SomaEraseFn efn = sup->type_desc ? sup->type_desc->erase_fn : NULL;

            switch (sup->tag) {
            case SUP_TAG_FRESH:
            case SUP_TAG_PROJ0:
            case SUP_TAG_PROJ1:
                if (SOMA_IS_PTR(v) && v != 0) {
                    if (efn != NULL) {
                        efn((void*)v);
                    } else {
                        ERA_ENSURE(1);
                        stack[sp++] = SOMA_TO_PTR(v);
                    }
                }
                break;

            case SUP_TAG_BOTH:
            default: {
                SomaValue p0 = (SomaValue)sup->proj0;
                SomaValue p1 = (SomaValue)sup->proj1;

                if (efn != NULL) {
                    if (SOMA_IS_PTR(v) && v != 0) efn((void*)v);
                    if (p0 != v && SOMA_IS_PTR(p0) && p0 != 0) efn((void*)p0);
                    if (p1 != v && p1 != p0 && SOMA_IS_PTR(p1) && p1 != 0) efn((void*)p1);
                } else {
                    ERA_ENSURE(2);
                    if (SOMA_IS_PTR(v) && v != 0) {
                        stack[sp++] = SOMA_TO_PTR(v);
                    }
                    if (p0 != v && SOMA_IS_PTR(p0) && p0 != 0) {
                        stack[sp++] = SOMA_TO_PTR(p0);
                    }
                    if (p1 != v && p1 != p0 && SOMA_IS_PTR(p1) && p1 != 0) {
                        stack[sp++] = SOMA_TO_PTR(p1);
                    }
                }
                break;
            }
            }

            SOMA_STAT_INC(sup_frees);
            pool_free(&pools->pool_48, cur);

        } else if (((uint8_t*)cur)[1] == NODE_CLOSURE) {
            SomaClosure* closure = (SomaClosure*)cur;
            uint16_t es = CLOSURE_ENV_SIZE(closure);
            void** env = (void**)(closure + 1);
            ERA_ENSURE(es);
            for (uint16_t i = 0; i < es; i++) {
                SomaValue sv = (SomaValue)(uintptr_t)env[i];
                if (SOMA_IS_PTR(sv) && sv != 0) {
                    stack[sp++] = SOMA_TO_PTR(sv);
                }
            }
            size_t needed = sizeof(SomaClosure) + es * sizeof(void*);
            if (SOMA_LIKELY(needed <= POOL_SIZE_48)) {
                SOMA_STAT_INC(small_frees);
                pool_free(&pools->pool_48, cur);
            } else if (needed <= POOL_SIZE_112) {
                SOMA_STAT_INC(medium_frees);
                pool_free(&pools->pool_112, cur);
            } else {
                SOMA_STAT_INC(large_frees);
                free(cur);
            }
        } else {
            soma_panic("soma_era_free: unrecognized heap object (missing typed eraser)");
        }

        #undef ERA_ENSURE
    }

    if (SOMA_UNLIKELY(stack != stack_buf)) {
        free(stack);
    }
}

SOMA_NORETURN SOMA_COLD
void soma_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg);
    soma_pool_cleanup();
    exit(1);
}


#ifndef SOMA_NO_MAIN
extern int soma_main(void);

int main(void) {
    soma_pool_init();
    int result = soma_main();
    soma_pool_cleanup();
    return result;
}
#endif
