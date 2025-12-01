/*
 * Soma Graph Reduction Runtime - Implementation
 */

#include "soma_graph.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <sched.h>  /* For sched_yield */

/* Debug support */
static int g_graph_debug = -1;
static inline int graph_debug_enabled(void) {
    if (g_graph_debug < 0) {
        g_graph_debug = (getenv("SOMA_GRAPH_DEBUG") != NULL) ? 1 : 0;
    }
    return g_graph_debug;
}
#define GDEBUG(...) do { if (graph_debug_enabled()) { fprintf(stderr, "[GRAPH] " __VA_ARGS__); } } while(0)

/* Global runtime instance */
GraphRuntime* g_graph_rt = NULL;

/*
 * Lifecycle
 */

GraphRuntime* soma_graph_init(int num_workers) {
    GraphRuntime* rt = calloc(1, sizeof(GraphRuntime));
    if (!rt) {
        fprintf(stderr, "soma_graph_init: failed to allocate runtime\n");
        return NULL;
    }
    
    /* Allocate node pool */
    rt->pool_size = GRAPH_NODE_POOL_SIZE;
    rt->nodes = calloc(rt->pool_size, sizeof(GNode));
    if (!rt->nodes) {
        fprintf(stderr, "soma_graph_init: failed to allocate node pool (%u nodes)\n", rt->pool_size);
        free(rt);
        return NULL;
    }
    
    /* Allocate parent array for worklist optimization */
    rt->parents = calloc(rt->pool_size, sizeof(uint32_t));
    if (!rt->parents) {
        fprintf(stderr, "soma_graph_init: failed to allocate parent array\n");
        free(rt->nodes);
        free(rt);
        return NULL;
    }
    /* Initialize all parents to GIDX_NULL */
    for (uint32_t i = 0; i < rt->pool_size; i++) {
        rt->parents[i] = GIDX_NULL;
    }
    
    atomic_store(&rt->next_alloc, 1);  /* Reserve index 0 as "null" */
    atomic_store(&rt->free_list_head, GIDX_NULL);  /* Empty free list */
    atomic_store(&rt->nodes_recycled, 0);
    atomic_store(&rt->nodes_reused, 0);
    
    /* Allocate argument overflow pool */
    rt->arg_pool_size = GRAPH_ARG_POOL_SIZE;
    rt->arg_pool = calloc(rt->arg_pool_size, sizeof(uint32_t));
    if (!rt->arg_pool) {
        fprintf(stderr, "soma_graph_init: failed to allocate arg pool\n");
        free(rt->nodes);
        free(rt);
        return NULL;
    }
    atomic_store(&rt->next_arg, 0);
    
    /* Allocate function table */
    rt->functions_capacity = 256;
    rt->functions = calloc(rt->functions_capacity, sizeof(GFunc));
    if (!rt->functions) {
        fprintf(stderr, "soma_graph_init: failed to allocate function table\n");
        free(rt->arg_pool);
        free(rt->nodes);
        free(rt);
        return NULL;
    }
    rt->num_functions = 0;
    
    /* Allocate redex buffers (legacy wavefront) */
    for (int i = 0; i < 2; i++) {
        rt->redex_buf[i] = calloc(GRAPH_REDEX_BUF_SIZE, sizeof(uint32_t));
        if (!rt->redex_buf[i]) {
            fprintf(stderr, "soma_graph_init: failed to allocate redex buffer %d\n", i);
            for (int j = 0; j < i; j++) free(rt->redex_buf[j]);
            free(rt->functions);
            free(rt->arg_pool);
            free(rt->nodes);
            free(rt);
            return NULL;
        }
        atomic_store(&rt->redex_count_padded[i].count, 0);
    }
    rt->current_buf = 0;
    
    /* Allocate worklist for fast reducer - needs to be larger than redex buf
     * because seeding can add many nodes at once */
    rt->worklist_capacity = GRAPH_NODE_POOL_SIZE / 4;  /* 16M nodes / 4 = 4M entries */
    rt->worklist = calloc(rt->worklist_capacity, sizeof(uint32_t));
    if (!rt->worklist) {
        fprintf(stderr, "soma_graph_init: failed to allocate worklist\n");
        free(rt->redex_buf[0]);
        free(rt->redex_buf[1]);
        free(rt->functions);
        free(rt->arg_pool);
        free(rt->nodes);
        free(rt);
        return NULL;
    }
    atomic_store(&rt->worklist_head, 0);
    atomic_store(&rt->worklist_tail, 0);
    
    /* Initialize workers (if parallel) */
    rt->num_workers = (num_workers > GRAPH_MAX_WORKERS) ? GRAPH_MAX_WORKERS : num_workers;
    
    /* Allocate per-worker deques and local buffers */
    for (int i = 0; i < rt->num_workers; i++) {
        rt->workers[i].deque = calloc(WORKER_DEQUE_SIZE, sizeof(uint32_t));
        rt->workers[i].local_buf = calloc(WORKER_LOCAL_BUF_SIZE, sizeof(uint32_t));
        if (!rt->workers[i].deque || !rt->workers[i].local_buf) {
            fprintf(stderr, "soma_graph_init: failed to allocate worker %d buffers\n", i);
            /* Clean up already allocated buffers */
            for (int j = 0; j <= i; j++) {
                if (rt->workers[j].deque) free(rt->workers[j].deque);
                if (rt->workers[j].local_buf) free(rt->workers[j].local_buf);
            }
            free(rt->worklist);
            free(rt->redex_buf[0]);
            free(rt->redex_buf[1]);
            free(rt->functions);
            free(rt->arg_pool);
            free(rt->parents);
            free(rt->nodes);
            free(rt);
            return NULL;
        }
        atomic_store(&rt->workers[i].deque_bottom, 0);
        atomic_store(&rt->workers[i].deque_top, 0);
        rt->workers[i].local_count = 0;
    }
    atomic_store(&rt->shutdown, 0);
    
    /* Statistics */
    atomic_store(&rt->total_reductions, 0);
    atomic_store(&rt->total_nodes, 0);
    atomic_store(&rt->wavefront_iterations, 0);
    
    g_graph_rt = rt;
    return rt;
}

void soma_graph_shutdown(GraphRuntime* rt) {
    if (!rt) return;
    
    /* Signal shutdown */
    atomic_store(&rt->shutdown, 1);
    
    /* Free worker deques and local buffers */
    for (int i = 0; i < rt->num_workers; i++) {
        if (rt->workers[i].deque) free(rt->workers[i].deque);
        if (rt->workers[i].local_buf) free(rt->workers[i].local_buf);
    }
    
    /* Free resources */
    free(rt->worklist);
    free(rt->redex_buf[0]);
    free(rt->redex_buf[1]);
    free(rt->functions);
    free(rt->arg_pool);
    free(rt->parents);
    free(rt->nodes);
    free(rt);
    
    if (g_graph_rt == rt) {
        g_graph_rt = NULL;
    }
}

/*
 * Node Allocation
 */

uint32_t soma_graph_alloc(GraphRuntime* rt) {
    /* First try to get a node from the free list */
    uint32_t head = atomic_load(&rt->free_list_head);
    while (head != GIDX_NULL) {
        /* The free node stores the next pointer in data.pair.l */
        uint32_t next = rt->nodes[head].data.pair.l;
        if (atomic_compare_exchange_weak(&rt->free_list_head, &head, next)) {
            /* Successfully popped from free list */
            rt->nodes[head].status = GSTAT_ACTIVE;
            atomic_fetch_add(&rt->nodes_reused, 1);
            return head;
        }
        /* CAS failed, head was updated by another thread, retry */
    }
    
    /* Free list empty, allocate from pool */
    uint32_t idx = atomic_fetch_add(&rt->next_alloc, 1);
    if (idx >= rt->pool_size) {
        fprintf(stderr, "soma_graph_alloc: node pool exhausted\n");
        return GIDX_NULL;
    }
    atomic_fetch_add(&rt->total_nodes, 1);
    return idx;
}

void soma_graph_free(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA || idx == 0) return;
    if (idx >= rt->next_alloc) return;
    
    /* Mark as free and add to free list */
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_ERA;  /* Mark as free (reuse ERA tag) */
    n->status = GSTAT_FREE;
    
    /* Push onto free list (lock-free stack) */
    uint32_t head = atomic_load(&rt->free_list_head);
    do {
        n->data.pair.l = head;  /* Store next pointer */
    } while (!atomic_compare_exchange_weak(&rt->free_list_head, &head, idx));
    
    atomic_fetch_add(&rt->nodes_recycled, 1);
}

uint32_t soma_graph_num(GraphRuntime* rt, int64_t value) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_NUM;
    n->status = GSTAT_DONE;  /* NUM is already a value */
    n->label = 0;
    n->aux = 0;
    n->data.num = value;
    rt->parents[idx] = GIDX_NULL;
    return idx;
}

uint32_t soma_graph_era(GraphRuntime* rt) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_ERA;
    n->status = GSTAT_DONE;  /* ERA is already a value */
    n->label = 0;
    n->aux = 0;
    n->data.num = 0;
    rt->parents[idx] = GIDX_NULL;
    return idx;
}

/* Helper for binary op allocation - sets parent links on children using PLINK encoding */
static inline uint32_t alloc_binop(GraphRuntime* rt, uint8_t tag, uint32_t left, uint32_t right) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = tag;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.pair.l = left;
    n->data.pair.r = right;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent links on children with slot encoding */
    if (left != GIDX_NULL && left != GIDX_ERA && left < rt->next_alloc) {
        rt->parents[left] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
    }
    if (right != GIDX_NULL && right != GIDX_ERA && right < rt->next_alloc) {
        rt->parents[right] = PLINK_MAKE(idx, PLINK_SLOT_RIGHT);
    }
    
    return idx;
}

uint32_t soma_graph_add(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_ADD, left, right);
}

uint32_t soma_graph_sub(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_SUB, left, right);
}

uint32_t soma_graph_mul(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_MUL, left, right);
}

uint32_t soma_graph_div(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_DIV, left, right);
}

uint32_t soma_graph_mod(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_MOD, left, right);
}

uint32_t soma_graph_eq(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_EQ, left, right);
}

uint32_t soma_graph_ne(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_NE, left, right);
}

uint32_t soma_graph_lt(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_LT, left, right);
}

uint32_t soma_graph_le(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_LE, left, right);
}

uint32_t soma_graph_gt(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_GT, left, right);
}

uint32_t soma_graph_ge(GraphRuntime* rt, uint32_t left, uint32_t right) {
    return alloc_binop(rt, GTAG_GE, left, right);
}

/*
 * Function-related nodes
 */

uint32_t soma_graph_call1(GraphRuntime* rt, uint16_t fn_idx, uint32_t arg0) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_CALL;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.call.fn = fn_idx;
    n->data.call.arity = 1;
    n->data.call.args = arg0;  /* Inline single arg */
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent link on arg with slot encoding */
    if (arg0 != GIDX_NULL && arg0 != GIDX_ERA && arg0 < rt->next_alloc) {
        rt->parents[arg0] = PLINK_MAKE(idx, PLINK_SLOT_ARG0);
    }
    
    return idx;
}

uint32_t soma_graph_call2(GraphRuntime* rt, uint16_t fn_idx, uint32_t arg0, uint32_t arg1) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    /* For 2 args, store in arg pool */
    uint32_t arg_idx = atomic_fetch_add(&rt->next_arg, 2);
    if (arg_idx + 2 > rt->arg_pool_size) {
        fprintf(stderr, "soma_graph_call2: arg pool exhausted\n");
        return GIDX_NULL;
    }
    rt->arg_pool[arg_idx] = arg0;
    rt->arg_pool[arg_idx + 1] = arg1;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_CALL;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.call.fn = fn_idx;
    n->data.call.arity = 2;
    n->data.call.args = arg_idx;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent links on args - for pool args we use PLINK_SLOT_LEFT/RIGHT as proxy */
    if (arg0 != GIDX_NULL && arg0 != GIDX_ERA && arg0 < rt->next_alloc) {
        rt->parents[arg0] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
    }
    if (arg1 != GIDX_NULL && arg1 != GIDX_ERA && arg1 < rt->next_alloc) {
        rt->parents[arg1] = PLINK_MAKE(idx, PLINK_SLOT_RIGHT);
    }
    
    return idx;
}

uint32_t soma_graph_call(GraphRuntime* rt, uint16_t fn_idx, uint32_t* args, int arity) {
    if (arity == 1) return soma_graph_call1(rt, fn_idx, args[0]);
    if (arity == 2) return soma_graph_call2(rt, fn_idx, args[0], args[1]);
    
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    /* Store args in overflow pool */
    uint32_t arg_idx = atomic_fetch_add(&rt->next_arg, arity);
    if (arg_idx + arity > rt->arg_pool_size) {
        fprintf(stderr, "soma_graph_call: arg pool exhausted\n");
        return GIDX_NULL;
    }
    for (int i = 0; i < arity; i++) {
        rt->arg_pool[arg_idx + i] = args[i];
    }
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_CALL;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.call.fn = fn_idx;
    n->data.call.arity = arity;
    n->data.call.args = arg_idx;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent links on args - use PLINK_SLOT_LEFT for all (can't direct-update pool args anyway) */
    for (int i = 0; i < arity; i++) {
        uint32_t arg = args[i];
        if (arg != GIDX_NULL && arg != GIDX_ERA && arg < rt->next_alloc) {
            rt->parents[arg] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
        }
    }
    
    return idx;
}

uint32_t soma_graph_ref(GraphRuntime* rt, uint16_t fn_idx) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_REF;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.ref = fn_idx;
    rt->parents[idx] = GIDX_NULL;
    return idx;
}

uint32_t soma_graph_app(GraphRuntime* rt, uint32_t fn, uint32_t arg) {
    return alloc_binop(rt, GTAG_APP, fn, arg);
}

uint32_t soma_graph_lam(GraphRuntime* rt, uint32_t var_slot, uint32_t body) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_LAM;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.lam.var = var_slot;
    n->data.lam.body = body;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent link on body with slot encoding */
    if (body != GIDX_NULL && body != GIDX_ERA && body < rt->next_alloc) {
        rt->parents[body] = PLINK_MAKE(idx, PLINK_SLOT_BODY);
    }
    
    return idx;
}

/*
 * Interaction net nodes
 */

uint32_t soma_graph_sup(GraphRuntime* rt, uint16_t label, uint32_t left, uint32_t right) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_SUP;
    n->status = GSTAT_ACTIVE;
    n->label = label;
    n->aux = 0;
    n->data.pair.l = left;
    n->data.pair.r = right;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent links on children with slot encoding */
    if (left != GIDX_NULL && left != GIDX_ERA && left < rt->next_alloc) {
        rt->parents[left] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
    }
    if (right != GIDX_NULL && right != GIDX_ERA && right < rt->next_alloc) {
        rt->parents[right] = PLINK_MAKE(idx, PLINK_SLOT_RIGHT);
    }
    
    return idx;
}

uint32_t soma_graph_dup(GraphRuntime* rt, uint16_t label, uint32_t target) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_DUP;
    n->status = GSTAT_ACTIVE;
    n->label = label;
    n->aux = 0;
    n->data.pair.l = target;
    n->data.pair.r = GIDX_NULL;  /* Projection slots filled during reduction */
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent link on target with slot encoding */
    if (target != GIDX_NULL && target != GIDX_ERA && target < rt->next_alloc) {
        rt->parents[target] = PLINK_MAKE(idx, PLINK_SLOT_TARGET);
    }
    
    return idx;
}

/*
 * ADT nodes
 */

uint32_t soma_graph_con(GraphRuntime* rt, uint16_t tag, uint32_t* fields, int arity) {
    uint32_t idx = soma_graph_alloc(rt);
    if (idx == GIDX_NULL) return GIDX_NULL;
    
    uint32_t fields_idx = GIDX_NULL;
    if (arity > 0) {
        fields_idx = atomic_fetch_add(&rt->next_arg, arity);
        if (fields_idx + arity > rt->arg_pool_size) {
            fprintf(stderr, "soma_graph_con: arg pool exhausted\n");
            return GIDX_NULL;
        }
        for (int i = 0; i < arity; i++) {
            rt->arg_pool[fields_idx + i] = fields[i];
        }
    }
    
    GNode* n = &rt->nodes[idx];
    n->tag = GTAG_CON;
    n->status = GSTAT_ACTIVE;
    n->label = 0;
    n->aux = 0;
    n->data.con.tag = tag;
    n->data.con.arity = arity;
    n->data.con.fields = fields_idx;
    rt->parents[idx] = GIDX_NULL;
    
    /* Set parent links on fields - use PLINK_SLOT_LEFT for pool fields */
    for (int i = 0; i < arity; i++) {
        uint32_t field = fields[i];
        if (field != GIDX_NULL && field != GIDX_ERA && field < rt->next_alloc) {
            rt->parents[field] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
        }
    }
    
    return idx;
}

/*
 * Function Table
 */

uint16_t soma_graph_register_func(GraphRuntime* rt, const char* name, 
                                   uint8_t arity, uint8_t flags, void* impl) {
    if (rt->num_functions >= rt->functions_capacity) {
        /* Grow table */
        uint32_t new_cap = rt->functions_capacity * 2;
        GFunc* new_table = realloc(rt->functions, new_cap * sizeof(GFunc));
        if (!new_table) {
            fprintf(stderr, "soma_graph_register_func: failed to grow function table\n");
            return 0xFFFF;
        }
        rt->functions = new_table;
        rt->functions_capacity = new_cap;
    }
    
    uint16_t idx = rt->num_functions++;
    GFunc* f = &rt->functions[idx];
    f->name = name;
    f->arity = arity;
    f->flags = flags;
    f->impl = impl;
    return idx;
}

GFunc* soma_graph_get_func(GraphRuntime* rt, uint16_t idx) {
    if (idx >= rt->num_functions) return NULL;
    return &rt->functions[idx];
}

/*
 * Single-Threaded Reduction
 */

/* Get argument for a CALL node */
static inline uint32_t get_call_arg(GraphRuntime* rt, GNode* n, int i) {
    if (n->data.call.arity == 1) {
        return n->data.call.args;  /* Inline */
    }
    /* Bounds check for parallel safety */
    uint32_t arg_idx = n->data.call.args + i;
    if (arg_idx >= rt->arg_pool_size) {
        return GIDX_NULL;  /* Invalid - node was corrupted/recycled */
    }
    return rt->arg_pool[arg_idx];
}

/* Check if all CALL args are values (following indirections) */
static int call_args_ready(GraphRuntime* rt, GNode* n) {
    int arity = n->data.call.arity;
    for (int i = 0; i < arity; i++) {
        uint32_t arg = get_call_arg(rt, n, i);
        if (!soma_graph_is_value(rt, arg)) {  /* soma_graph_is_value follows indirections */
            return 0;
        }
    }
    return 1;
}

/* Typedef for graph-building functions */
typedef uint32_t (*GraphFn1)(GraphRuntime* rt, int64_t arg0);
typedef uint32_t (*GraphFn2)(GraphRuntime* rt, int64_t arg0, int64_t arg1);

/* Try to claim a node for reduction using CAS (returns 1 if claimed, 0 if already claimed/done)
 * HVM3 insight: Use single CAS on status to prevent duplicate work */
static inline int try_claim_node(GraphRuntime* rt, uint32_t idx) {
    GNode* n = &rt->nodes[idx];
    uint8_t expected = GSTAT_ACTIVE;
    /* CAS: if status == ACTIVE, set to REDUCING and return true */
    return atomic_compare_exchange_strong_explicit(
        (_Atomic uint8_t*)&n->status,
        &expected,
        GSTAT_REDUCING,
        memory_order_acquire,
        memory_order_relaxed
    );
}

/* Reduce a single node, returns 1 if reduced, 0 if blocked or already value */
int soma_graph_reduce_node(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return 0;
    if (idx >= rt->next_alloc) return 0;
    
    GNode* n = &rt->nodes[idx];
    
    /* Already a value or being reduced? */
    if (n->status == GSTAT_DONE || n->status == GSTAT_REDUCING) return 0;
    
    switch (n->tag) {
        case GTAG_NUM:
        case GTAG_ERA:
            n->status = GSTAT_DONE;
            return 0;  /* Already a value */
            
        case GTAG_ADD:
        case GTAG_SUB:
        case GTAG_MUL:
        case GTAG_DIV:
        case GTAG_MOD:
        case GTAG_EQ:
        case GTAG_NE:
        case GTAG_LT:
        case GTAG_LE:
        case GTAG_GT:
        case GTAG_GE: {
            /* Follow indirections to get actual children */
            uint32_t l_idx = soma_graph_deref(rt, n->data.pair.l);
            uint32_t r_idx = soma_graph_deref(rt, n->data.pair.r);
            
            /* Both must be values */
            if (!soma_graph_is_value(rt, l_idx) || !soma_graph_is_value(rt, r_idx)) {
                return 0;  /* Blocked */
            }
            
            /* Try to claim this node for reduction (atomic) */
            if (!try_claim_node(rt, idx)) {
                return 0;  /* Someone else is reducing it */
            }
            
            /* Read values atomically to prevent torn reads during concurrent reduction */
            int64_t l_val = atomic_load((_Atomic int64_t*)&rt->nodes[l_idx].data.num);
            int64_t r_val = atomic_load((_Atomic int64_t*)&rt->nodes[r_idx].data.num);
            int64_t result;
            
            switch (n->tag) {
                case GTAG_ADD: result = l_val + r_val; break;
                case GTAG_SUB: result = l_val - r_val; break;
                case GTAG_MUL: result = l_val * r_val; break;
                case GTAG_DIV: result = (r_val != 0) ? l_val / r_val : 0; break;
                case GTAG_MOD: result = (r_val != 0) ? l_val % r_val : 0; break;
                case GTAG_EQ:  result = (l_val == r_val) ? 1 : 0; break;
                case GTAG_NE:  result = (l_val != r_val) ? 1 : 0; break;
                case GTAG_LT:  result = (l_val < r_val) ? 1 : 0; break;
                case GTAG_LE:  result = (l_val <= r_val) ? 1 : 0; break;
                case GTAG_GT:  result = (l_val > r_val) ? 1 : 0; break;
                case GTAG_GE:  result = (l_val >= r_val) ? 1 : 0; break;
                default: result = 0;
            }
            
            /* HVM3 optimization: In-place mutation to NUM
             * Since we claimed this node with CAS, we have exclusive write access.
             * Use relaxed store for data (only we write), release for status (visibility). */
            n->tag = GTAG_NUM;
            n->data.num = result;
            atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
            atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
            return 1;
        }
        
        case GTAG_CALL: {
            /* Check if all args are ready (following indirections) */
            if (!call_args_ready(rt, n)) {
                return 0;  /* Blocked */
            }
            
            /* Try to claim this node for reduction (atomic) */
            if (!try_claim_node(rt, idx)) {
                return 0;  /* Someone else is reducing it */
            }
            
            GFunc* fn = soma_graph_get_func(rt, n->data.call.fn);
            if (!fn) {
                fprintf(stderr, "soma_graph_reduce_node: invalid function index %u\n", n->data.call.fn);
                n->tag = GTAG_ERA;
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                return 1;
            }
            
            int arity = n->data.call.arity;
            
            /* Collect arg values (follow indirections) and free arg nodes */
            int64_t arg_vals[4];  /* Support up to 4 args inline */
            for (int i = 0; i < arity && i < 4; i++) {
                uint32_t arg_idx = soma_graph_deref(rt, get_call_arg(rt, n, i));
                arg_vals[i] = rt->nodes[arg_idx].data.num;
                /* Don't free args here - they might be shared via indirections */
            }
            
            /* Dispatch based on arity */
            uint32_t result_idx;
            if (arity == 1) {
                GraphFn1 fn1 = (GraphFn1)fn->impl;
                result_idx = fn1(rt, arg_vals[0]);
            } else if (arity == 2) {
                GraphFn2 fn2 = (GraphFn2)fn->impl;
                result_idx = fn2(rt, arg_vals[0], arg_vals[1]);
            } else {
                /* For higher arities, would need more function typedefs */
                fprintf(stderr, "soma_graph_reduce_node: arity %d not yet supported\n", arity);
                n->tag = GTAG_ERA;
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                return 1;
            }
            
            /* HVM3-style: Direct pointer update instead of IND node.
             * Update parent's child pointer to point directly to result.
             * This eliminates indirection chains entirely.
             * 
             * NOTE: Only do this in single-threaded mode. In parallel mode,
             * the wavefront code expects IND nodes to propagate work. */
            uint32_t plink = rt->parents[idx];
            int use_direct_update = (rt->num_workers <= 1) && 
                                    (plink != GIDX_NULL);
            
            if (use_direct_update) {
                /* Update parent to point to result directly */
                soma_graph_update_parent(rt, plink, result_idx);
                
                /* Recycle this CALL node since it's no longer referenced */
                soma_graph_free(rt, idx);
                
                /* Update result's parent link */
                if (result_idx != GIDX_NULL && result_idx != GIDX_ERA && result_idx < rt->next_alloc) {
                    atomic_store_explicit((_Atomic uint32_t*)&rt->parents[result_idx], plink, memory_order_relaxed);
                }
            } else {
                /* Use IND node for parallel compatibility or root nodes */
                n->tag = GTAG_IND;
                n->data.pair.l = result_idx;
                n->data.pair.r = GIDX_NULL;
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                
                /* Update result's parent to point through us */
                if (result_idx != GIDX_NULL && result_idx != GIDX_ERA && result_idx < rt->next_alloc) {
                    rt->parents[result_idx] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
                }
            }
            
            atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
            return 1;
        }
        
        /*
         * APP-LAM: Beta reduction
         * APP(LAM(var, body), arg) → body[var := arg]
         * 
         * In our representation:
         * - APP node has fn (left) and arg (right)
         * - LAM node has var slot and body
         * - We substitute by creating an IND from var to arg
         */
        case GTAG_APP: {
            uint32_t fn_idx = soma_graph_deref(rt, n->data.pair.l);
            uint32_t arg_idx = n->data.pair.r;
            
            if (fn_idx == GIDX_NULL || fn_idx >= rt->next_alloc) return 0;
            
            GNode* fn_node = &rt->nodes[fn_idx];
            
            /* APP-LAM: fn must be a LAM node */
            if (fn_node->tag != GTAG_LAM) {
                return 0;  /* Blocked - fn is not yet a lambda */
            }
            
            /* Try to claim this APP node */
            if (!try_claim_node(rt, idx)) {
                return 0;
            }
            
            /* Get lambda's var slot and body */
            uint32_t var_slot = fn_node->data.lam.var;
            uint32_t body_idx = fn_node->data.lam.body;
            
            /* Substitute: For var_slot, we need to update places that reference it.
             * In HVM3 style, var references are updated directly. For now, use IND
             * since var slots can be referenced multiple times in the body. */
            if (var_slot != GIDX_NULL && var_slot < rt->next_alloc) {
                GNode* var_node = &rt->nodes[var_slot];
                var_node->tag = GTAG_IND;
                var_node->data.pair.l = arg_idx;
                var_node->data.pair.r = GIDX_NULL;
                atomic_store_explicit((_Atomic uint8_t*)&var_node->status, GSTAT_DONE, memory_order_release);
            }
            
            /* HVM3-style: Direct pointer update for the APP node itself.
             * Only in single-threaded mode - parallel modes need IND for propagation. */
            uint32_t plink = rt->parents[idx];
            int use_direct_update = (rt->num_workers <= 1) && 
                                    (plink != GIDX_NULL);
            
            if (use_direct_update) {
                /* Update parent to point to body directly */
                soma_graph_update_parent(rt, plink, body_idx);
                
                /* Recycle this APP node */
                soma_graph_free(rt, idx);
                
                /* Update body's parent link */
                if (body_idx != GIDX_NULL && body_idx < rt->next_alloc) {
                    atomic_store_explicit((_Atomic uint32_t*)&rt->parents[body_idx], plink, memory_order_relaxed);
                }
            } else {
                /* Use IND node for parallel compatibility or root nodes */
                n->tag = GTAG_IND;
                n->data.pair.l = body_idx;
                n->data.pair.r = GIDX_NULL;
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                
                /* Update body's parent to point through us */
                if (body_idx != GIDX_NULL && body_idx < rt->next_alloc) {
                    rt->parents[body_idx] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
                }
            }
            
            atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
            return 1;
        }
        
        /*
         * DUP-SUP Interaction Rules (Core of Interaction Nets)
         * 
         * DUP[L] on SUP[L] (same label): Annihilation
         *   !d &L = &L{a, b}  →  d.0 := a, d.1 := b
         * 
         * DUP[L] on SUP[M] (different labels): Commutation  
         *   !d &L = &M{a, b}  →  d.0 := &M{a.0, b.0}, d.1 := &M{a.1, b.1}
         *   where a.0, a.1 are projections from duplicating a with label L
         *
         * In our representation:
         * - DUP node: label in n->label, target in data.pair.l
         *             data.pair.r stores the "second slot" for projections (optional)
         * - SUP node: label in n->label, left in data.pair.l, right in data.pair.r
         */
        case GTAG_DUP: {
            uint32_t target_idx = soma_graph_deref(rt, n->data.pair.l);
            
            if (target_idx == GIDX_NULL || target_idx >= rt->next_alloc) {
                /* DUP of null/invalid - treat as erased */
                if (!try_claim_node(rt, idx)) return 0;
                n->tag = GTAG_ERA;
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                return 1;
            }
            
            GNode* target = &rt->nodes[target_idx];
            
            /* DUP-NUM: Duplicate a number - just copy */
            if (target->tag == GTAG_NUM) {
                if (!try_claim_node(rt, idx)) return 0;
                
                /* Create SUP with two copies of the number */
                int64_t val = target->data.num;
                uint32_t copy1 = soma_graph_num(rt, val);
                uint32_t copy2 = soma_graph_num(rt, val);
                
                /* Turn DUP into SUP */
                n->tag = GTAG_SUP;
                /* Keep the same label */
                n->data.pair.l = copy1;
                n->data.pair.r = copy2;
                
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
                return 1;
            }
            
            /* DUP-ERA: Duplicate erasure - both projections are erasure */
            if (target->tag == GTAG_ERA) {
                if (!try_claim_node(rt, idx)) return 0;
                
                /* Create SUP with two ERA nodes */
                uint32_t era1 = soma_graph_era(rt);
                uint32_t era2 = soma_graph_era(rt);
                
                n->tag = GTAG_SUP;
                n->data.pair.l = era1;
                n->data.pair.r = era2;
                
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
                return 1;
            }
            
            /* DUP-SUP: Core interaction */
            if (target->tag == GTAG_SUP) {
                if (!try_claim_node(rt, idx)) return 0;
                
                uint16_t dup_label = n->label;
                uint16_t sup_label = target->label;
                uint32_t sup_left = target->data.pair.l;
                uint32_t sup_right = target->data.pair.r;
                
                if (dup_label == sup_label) {
                    /* ANNIHILATION: Same label - direct substitution
                     * DUP[L] on SUP[L]{a, b} → (a, b) directly */
                    n->tag = GTAG_SUP;
                    n->data.pair.l = sup_left;
                    n->data.pair.r = sup_right;
                    /* Label stays the same */
                    
                    atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_DONE, memory_order_release);
                    atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
                    return 1;
                } else {
                    /* COMMUTATION: Different labels - create nested structure
                     * DUP[L] on SUP[M]{a, b} → SUP[M]{DUP[L](a), DUP[L](b)}
                     * After both inner DUPs reduce, we get:
                     * SUP[M]{SUP[L]{a0, a1}, SUP[L]{b0, b1}}
                     */
                    
                    /* Create DUP nodes for left and right */
                    uint32_t dup_left = soma_graph_dup(rt, dup_label, sup_left);
                    uint32_t dup_right = soma_graph_dup(rt, dup_label, sup_right);
                    
                    /* Turn this node into SUP[M]{dup_left, dup_right} */
                    n->tag = GTAG_SUP;
                    n->label = sup_label;  /* Use the inner SUP's label */
                    n->data.pair.l = dup_left;
                    n->data.pair.r = dup_right;
                    
                    /* Set parents for new DUP nodes with PLINK encoding */
                    if (dup_left != GIDX_NULL) rt->parents[dup_left] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
                    if (dup_right != GIDX_NULL) rt->parents[dup_right] = PLINK_MAKE(idx, PLINK_SLOT_RIGHT);
                    
                    atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_ACTIVE, memory_order_release);
                    atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
                    return 1;
                }
            }
            
            /* DUP-LAM: Duplicate a lambda 
             * !d &L = λx.body → d.0 := λx0.body0, d.1 := λx1.body1
             * where x := SUP[L]{x0, x1} and body is duplicated
             */
            if (target->tag == GTAG_LAM) {
                if (!try_claim_node(rt, idx)) return 0;
                
                uint16_t dup_label = n->label;
                uint32_t old_var = target->data.lam.var;
                uint32_t old_body = target->data.lam.body;
                
                /* Create new variable slots for the two copies */
                uint32_t var0 = soma_graph_alloc(rt);
                uint32_t var1 = soma_graph_alloc(rt);
                if (var0 == GIDX_NULL || var1 == GIDX_NULL) return 0;
                
                /* Initialize as placeholder nodes (will be substituted later) */
                rt->nodes[var0].tag = GTAG_NUM;
                rt->nodes[var0].status = GSTAT_ACTIVE;
                rt->nodes[var0].data.num = 0;
                rt->nodes[var1].tag = GTAG_NUM;
                rt->nodes[var1].status = GSTAT_ACTIVE;
                rt->nodes[var1].data.num = 0;
                
                /* Make old var point to SUP of new vars */
                if (old_var != GIDX_NULL && old_var < rt->next_alloc) {
                    GNode* old_var_node = &rt->nodes[old_var];
                    old_var_node->tag = GTAG_SUP;
                    old_var_node->label = dup_label;
                    old_var_node->data.pair.l = var0;
                    old_var_node->data.pair.r = var1;
                    old_var_node->status = GSTAT_DONE;
                }
                
                /* Duplicate the body */
                uint32_t body_dup = soma_graph_dup(rt, dup_label, old_body);
                
                /* Create two new LAM nodes */
                uint32_t lam0 = soma_graph_lam(rt, var0, body_dup);  /* Will get proj0 of body_dup */
                uint32_t lam1 = soma_graph_lam(rt, var1, body_dup);  /* Will get proj1 of body_dup */
                
                /* Turn this DUP into SUP of the two lambdas */
                n->tag = GTAG_SUP;
                n->data.pair.l = lam0;
                n->data.pair.r = lam1;
                
                /* Set parents with PLINK encoding */
                if (lam0 != GIDX_NULL) rt->parents[lam0] = PLINK_MAKE(idx, PLINK_SLOT_LEFT);
                if (lam1 != GIDX_NULL) rt->parents[lam1] = PLINK_MAKE(idx, PLINK_SLOT_RIGHT);
                
                atomic_store_explicit((_Atomic uint8_t*)&n->status, GSTAT_ACTIVE, memory_order_release);
                atomic_fetch_add_explicit(&rt->total_reductions, 1, memory_order_relaxed);
                return 1;
            }
            
            /* Target not ready for duplication yet */
            return 0;
        }
        
        /* LAM nodes are values - they don't reduce on their own */
        case GTAG_LAM:
            n->status = GSTAT_DONE;
            return 0;
        
        /* SUP nodes are values (superpositions) - they reduce when DUP interacts */
        case GTAG_SUP:
            n->status = GSTAT_DONE;
            return 0;
        
        /* IND nodes are transparent - follow the chain */
        case GTAG_IND:
            n->status = GSTAT_DONE;
            return 0;
        
        default:
            return 0;  /* Unknown tag, treat as blocked */
    }
}

/* Add a node to the next redex buffer */
static inline void add_redex(GraphRuntime* rt, int buf, uint32_t idx) {
    uint32_t pos = atomic_fetch_add(&rt->redex_count_padded[buf].count, 1);
    if (pos < GRAPH_REDEX_BUF_SIZE) {
        rt->redex_buf[buf][pos] = idx;
    }
}

/* Find reducible children and add them to redex buffer */
static void find_redexes(GraphRuntime* rt, uint32_t idx, int buf) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return;
    if (idx >= rt->next_alloc) return;
    
    GNode* n = &rt->nodes[idx];
    if (n->status == GSTAT_DONE) return;
    
    switch (n->tag) {
        case GTAG_ADD:
        case GTAG_SUB:
        case GTAG_MUL:
        case GTAG_DIV:
        case GTAG_MOD:
        case GTAG_EQ:
        case GTAG_NE:
        case GTAG_LT:
        case GTAG_LE:
        case GTAG_GT:
        case GTAG_GE: {
            uint32_t l_idx = n->data.pair.l;
            uint32_t r_idx = n->data.pair.r;
            int l_val = soma_graph_is_value(rt, l_idx);
            int r_val = soma_graph_is_value(rt, r_idx);
            
            if (l_val && r_val) {
                /* This node is reducible */
                add_redex(rt, buf, idx);
            } else {
                /* Recurse into non-value children */
                if (!l_val) find_redexes(rt, l_idx, buf);
                if (!r_val) find_redexes(rt, r_idx, buf);
            }
            break;
        }
        
        case GTAG_CALL: {
            if (call_args_ready(rt, n)) {
                add_redex(rt, buf, idx);
            } else {
                /* Recurse into non-value args */
                int arity = n->data.call.arity;
                for (int i = 0; i < arity; i++) {
                    uint32_t arg = get_call_arg(rt, n, i);
                    if (!soma_graph_is_value(rt, arg)) {
                        find_redexes(rt, arg, buf);
                    }
                }
            }
            break;
        }
        
        case GTAG_APP: {
            /* APP is reducible when fn is a LAM */
            uint32_t fn_idx = soma_graph_deref(rt, n->data.pair.l);
            if (fn_idx != GIDX_NULL && fn_idx < rt->next_alloc && 
                rt->nodes[fn_idx].tag == GTAG_LAM) {
                add_redex(rt, buf, idx);
            } else {
                /* Recurse into fn and arg */
                find_redexes(rt, n->data.pair.l, buf);
                find_redexes(rt, n->data.pair.r, buf);
            }
            break;
        }
        
        case GTAG_DUP: {
            /* DUP is reducible when target is NUM, ERA, SUP, or LAM */
            uint32_t target_idx = soma_graph_deref(rt, n->data.pair.l);
            if (target_idx == GIDX_NULL || target_idx >= rt->next_alloc) {
                add_redex(rt, buf, idx);  /* DUP of null is reducible */
            } else {
                uint8_t target_tag = rt->nodes[target_idx].tag;
                if (target_tag == GTAG_NUM || target_tag == GTAG_ERA ||
                    target_tag == GTAG_SUP || target_tag == GTAG_LAM) {
                    add_redex(rt, buf, idx);
                } else {
                    /* Recurse into target */
                    find_redexes(rt, n->data.pair.l, buf);
                }
            }
            break;
        }
        
        case GTAG_SUP:
            /* SUP is a value, but children might have reducibles */
            find_redexes(rt, n->data.pair.l, buf);
            find_redexes(rt, n->data.pair.r, buf);
            break;
        
        case GTAG_LAM:
            /* LAM is a value, but body might have reducibles */
            find_redexes(rt, n->data.lam.body, buf);
            break;
        
        case GTAG_IND:
            /* Follow indirection */
            find_redexes(rt, n->data.pair.l, buf);
            break;
        
        default:
            break;
    }
}

/* Single-threaded reduce until root is a value */
int64_t soma_graph_reduce(GraphRuntime* rt, uint32_t root) {
    if (root == GIDX_NULL || root == GIDX_ERA) return 0;
    
    int iterations = 0;
    int max_iterations = 1000000000;  /* Safety limit */
    
    while (!soma_graph_is_value(rt, root) && iterations < max_iterations) {
        /* Find all reducible nodes */
        int cur = rt->current_buf;
        atomic_store(&rt->redex_count_padded[cur].count, 0);
        find_redexes(rt, root, cur);
        
        uint32_t count = atomic_load(&rt->redex_count_padded[cur].count);
        if (count == 0) {
            /* No progress possible - stuck */
            fprintf(stderr, "soma_graph_reduce: stuck after %d iterations\n", iterations);
            break;
        }
        
        /* Reduce all redexes */
        for (uint32_t i = 0; i < count; i++) {
            soma_graph_reduce_node(rt, rt->redex_buf[cur][i]);
        }
        
        iterations++;
        atomic_fetch_add(&rt->wavefront_iterations, 1);
    }
    
    if (soma_graph_is_value(rt, root)) {
        return rt->nodes[root].data.num;
    }
    
    fprintf(stderr, "soma_graph_reduce: failed to reduce to value\n");
    return 0;
}

/*
 * Worklist-based fast reducer
 * 
 * Key insight: Instead of traversing the entire tree each iteration to find
 * reducible nodes, we maintain a worklist. When a node is reduced to a value,
 * we check if its parent is now reducible and add it to the worklist.
 * 
 * This gives us O(reductions) work instead of O(nodes * iterations).
 */

/* Add a node to the worklist (circular buffer) */
static inline void worklist_push(GraphRuntime* rt, uint32_t idx) {
    uint32_t tail = atomic_load(&rt->worklist_tail);
    uint32_t next_tail = (tail + 1) % rt->worklist_capacity;
    
    /* Check if full (head == next_tail means full) */
    if (next_tail == atomic_load(&rt->worklist_head)) {
        /* Worklist full - this shouldn't happen with proper sizing */
        fprintf(stderr, "worklist_push: worklist full\n");
        return;
    }
    
    rt->worklist[tail] = idx;
    atomic_store(&rt->worklist_tail, next_tail);
}

/* Pop a node from the worklist, returns GIDX_NULL if empty */
static inline uint32_t worklist_pop(GraphRuntime* rt) {
    uint32_t head = atomic_load(&rt->worklist_head);
    if (head == atomic_load(&rt->worklist_tail)) {
        return GIDX_NULL;  /* Empty */
    }
    
    uint32_t idx = rt->worklist[head];
    atomic_store(&rt->worklist_head, (head + 1) % rt->worklist_capacity);
    return idx;
}

/* Check if a node is reducible (all children are values, following indirections) */
static int is_reducible(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return 0;
    if (idx >= rt->next_alloc) return 0;
    
    GNode* n = &rt->nodes[idx];
    if (n->status == GSTAT_DONE || n->status == GSTAT_REDUCING) return 0;
    
    switch (n->tag) {
        case GTAG_ADD:
        case GTAG_SUB:
        case GTAG_MUL:
        case GTAG_DIV:
        case GTAG_MOD:
        case GTAG_EQ:
        case GTAG_NE:
        case GTAG_LT:
        case GTAG_LE:
        case GTAG_GT:
        case GTAG_GE:
            /* soma_graph_is_value already follows indirections */
            return soma_graph_is_value(rt, n->data.pair.l) && 
                   soma_graph_is_value(rt, n->data.pair.r);
        
        case GTAG_CALL:
            return call_args_ready(rt, n);
        
        case GTAG_APP: {
            /* APP is reducible when fn is a LAM (beta reduction) */
            uint32_t fn_idx = soma_graph_deref(rt, n->data.pair.l);
            if (fn_idx == GIDX_NULL || fn_idx >= rt->next_alloc) return 0;
            return rt->nodes[fn_idx].tag == GTAG_LAM;
        }
        
        case GTAG_DUP: {
            /* DUP is reducible when target is a value or another reducible form */
            uint32_t target_idx = soma_graph_deref(rt, n->data.pair.l);
            if (target_idx == GIDX_NULL || target_idx >= rt->next_alloc) return 1;  /* DUP of null is reducible */
            uint8_t target_tag = rt->nodes[target_idx].tag;
            /* DUP can reduce on NUM, ERA, SUP, or LAM */
            return target_tag == GTAG_NUM || target_tag == GTAG_ERA || 
                   target_tag == GTAG_SUP || target_tag == GTAG_LAM;
        }
        
        default:
            return 0;
    }
}

/* Seed the worklist with all initially reducible nodes (leaf operations) */
static void seed_worklist(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return;
    if (idx >= rt->next_alloc) return;
    
    GNode* n = &rt->nodes[idx];
    
    /* Follow indirections */
    if (n->tag == GTAG_IND) {
        seed_worklist(rt, n->data.pair.l);
        return;
    }
    
    /* Skip if already done or being reduced */
    uint8_t status = atomic_load((_Atomic uint8_t*)&n->status);
    if (status == GSTAT_DONE || status == GSTAT_REDUCING) return;
    
    /* If this node is reducible, add it */
    if (is_reducible(rt, idx)) {
        worklist_push(rt, idx);
        return;
    }
    
    /* Otherwise, recurse into children */
    switch (n->tag) {
        case GTAG_ADD:
        case GTAG_SUB:
        case GTAG_MUL:
        case GTAG_DIV:
        case GTAG_MOD:
        case GTAG_EQ:
        case GTAG_NE:
        case GTAG_LT:
        case GTAG_LE:
        case GTAG_GT:
        case GTAG_GE:
            seed_worklist(rt, n->data.pair.l);
            seed_worklist(rt, n->data.pair.r);
            break;
        
        case GTAG_APP:
            /* For APP, recurse into fn (might become LAM) and arg */
            seed_worklist(rt, n->data.pair.l);
            seed_worklist(rt, n->data.pair.r);
            break;
        
        case GTAG_DUP:
            /* For DUP, recurse into target */
            seed_worklist(rt, n->data.pair.l);
            break;
        
        case GTAG_SUP:
            /* SUP is a value, but recurse into children in case they're not */
            seed_worklist(rt, n->data.pair.l);
            seed_worklist(rt, n->data.pair.r);
            break;
        
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            for (int i = 0; i < arity; i++) {
                seed_worklist(rt, get_call_arg(rt, n, i));
            }
            break;
        }
        
        case GTAG_LAM:
            /* LAM is a value, but body might have reducible nodes */
            seed_worklist(rt, n->data.lam.body);
            break;
        
        default:
            break;
    }
}

/* Reduce a node and propagate to parent if parent becomes reducible */
static void reduce_and_propagate(GraphRuntime* rt, uint32_t idx) {
    if (!soma_graph_reduce_node(rt, idx)) {
        return;  /* Not reduced */
    }
    
    GNode* n = &rt->nodes[idx];
    
    /* If node became an IND, seed from its target */
    if (n->tag == GTAG_IND) {
        uint32_t target = n->data.pair.l;
        if (target != GIDX_NULL && target < rt->next_alloc) {
            /* Add target to worklist if reducible, or recurse */
            if (is_reducible(rt, target)) {
                worklist_push(rt, target);
            } else {
                seed_worklist(rt, target);
            }
        }
    }
    
    /* Node was reduced - check if parent is now reducible.
     * Note: plink == GIDX_NULL means no parent. PLINK_GET_INDEX extracts
     * the parent index from the encoded plink value. */
    uint32_t plink = rt->parents[idx];
    if (plink == GIDX_NULL) return;  /* No parent */
    
    uint32_t parent = PLINK_GET_INDEX(plink);
    if (parent < rt->next_alloc) {
        if (is_reducible(rt, parent)) {
            worklist_push(rt, parent);
        }
    }
}

/* Fast worklist-based reduction */
int64_t soma_graph_reduce_fast(GraphRuntime* rt, uint32_t root) {
    if (root == GIDX_NULL || root == GIDX_ERA) return 0;
    
    /* Reset worklist */
    atomic_store(&rt->worklist_head, 0);
    atomic_store(&rt->worklist_tail, 0);
    
    /* Seed worklist with initially reducible nodes */
    seed_worklist(rt, root);
    
    /* Process worklist until empty and root is a value */
    uint64_t iterations = 0;
    while (!soma_graph_is_value(rt, root)) {
        uint32_t idx = worklist_pop(rt);
        
        if (idx == GIDX_NULL) {
            /* Worklist empty but root not a value - might need to re-seed
             * This can happen if parent pointers get stale after node reuse */
            seed_worklist(rt, root);
            idx = worklist_pop(rt);
            if (idx == GIDX_NULL) {
                fprintf(stderr, "soma_graph_reduce_fast: stuck, no reducible nodes\n");
                break;
            }
        }
        
        reduce_and_propagate(rt, idx);
        iterations++;
        
        /* Safety limit */
        if (iterations > 10000000000ULL) {
            fprintf(stderr, "soma_graph_reduce_fast: iteration limit exceeded\n");
            break;
        }
    }
    
    atomic_store(&rt->wavefront_iterations, iterations);
    
    /* Follow indirections to get final value */
    uint32_t final_idx = soma_graph_deref(rt, root);
    if (soma_graph_is_value(rt, final_idx)) {
        return rt->nodes[final_idx].data.num;
    }
    
    fprintf(stderr, "soma_graph_reduce_fast: failed to reduce to value\n");
    return 0;
}

/*
 * Parallel Reduction - HVM-style Atomic Redex Bag
 * 
 * HVM's approach:
 * 1. Double-buffered redex bags (current iteration / next iteration)
 * 2. Workers atomically grab indices from current bag
 * 3. Workers write new redexes to next bag
 * 4. Barrier sync, then swap bags
 * 
 * This gives coarse-grained batching - one atomic per batch of work,
 * not one atomic per node.
 */

#define BATCH_SIZE 1024  /* Nodes to grab at once - larger = less contention */

/* Worker grabs a batch of work from the current redex buffer */
static inline uint32_t grab_batch_start(GraphRuntime* rt) {
    int cur = rt->current_buf;
    uint32_t count = atomic_load(&rt->redex_count_padded[cur].count);
    if (count == 0) return GIDX_NULL;
    
    /* Atomically grab BATCH_SIZE items */
    uint32_t start = atomic_fetch_add(&rt->next_redex_padded.value, BATCH_SIZE);
    if (start >= count) return GIDX_NULL;
    return start;
}

/* Forward declaration */
static void flush_local_buffer(GraphRuntime* rt, GWorker* w);

/* Add to worker's local buffer. If buffer is nearly full, flush to global. */
static inline void local_add_redex_rt(GraphRuntime* rt, GWorker* w, uint32_t idx) {
    /* Flush if buffer is 75% full */
    if (w->local_count >= (WORKER_LOCAL_BUF_SIZE * 3 / 4)) {
        flush_local_buffer(rt, w);
    }
    if (w->local_count < WORKER_LOCAL_BUF_SIZE) {
        w->local_buf[w->local_count++] = idx;
    }
}

/* Simple version without runtime pointer (for use in seed_redex_buf_local) */
static inline void local_add_redex(GWorker* w, uint32_t idx) {
    if (w->local_count < WORKER_LOCAL_BUF_SIZE) {
        w->local_buf[w->local_count++] = idx;
    }
}

/* Forward declaration for get_call_arg */
static inline uint32_t get_call_arg(GraphRuntime* rt, GNode* n, int i);

/* Seed reducible nodes from a newly built subgraph into worker's local buffer.
 * Only seeds 1-2 levels deep to avoid buffer explosion. For fib, this is enough
 * because graph_fib returns ADD(CALL, CALL) where both CALLs have NUM args. */
static void seed_redex_buf_local(GraphRuntime* rt, GWorker* w, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return;
    if (idx >= rt->next_alloc) return;
    
    GNode* n = &rt->nodes[idx];
    
    /* Follow indirections */
    while (n->tag == GTAG_IND) {
        idx = n->data.pair.l;
        if (idx == GIDX_NULL || idx >= rt->next_alloc) return;
        n = &rt->nodes[idx];
    }
    
    uint8_t status = atomic_load_explicit((_Atomic uint8_t*)&n->status, memory_order_relaxed);
    if (status == GSTAT_DONE || status == GSTAT_REDUCING) return;
    
    /* If the root itself is reducible, add it */
    if (is_reducible(rt, idx)) {
        local_add_redex(w, idx);
        return;
    }
    
    /* If it's a value, nothing to do */
    if (n->tag == GTAG_NUM || n->tag == GTAG_ERA) {
        return;
    }
    
    /* The root is not reducible. Recurse into children to find reducible nodes. */
    switch (n->tag) {
        case GTAG_ADD: case GTAG_SUB: case GTAG_MUL: case GTAG_DIV: case GTAG_MOD:
        case GTAG_EQ: case GTAG_NE: case GTAG_LT: case GTAG_LE: case GTAG_GT: case GTAG_GE: {
            uint32_t l = soma_graph_deref(rt, n->data.pair.l);
            uint32_t r = soma_graph_deref(rt, n->data.pair.r);
            if (l != GIDX_NULL && l < rt->next_alloc && is_reducible(rt, l)) {
                local_add_redex(w, l);
            }
            if (r != GIDX_NULL && r < rt->next_alloc && is_reducible(rt, r)) {
                local_add_redex(w, r);
            }
            break;
        }
        case GTAG_APP: {
            uint32_t fn = soma_graph_deref(rt, n->data.pair.l);
            uint32_t arg = soma_graph_deref(rt, n->data.pair.r);
            if (fn != GIDX_NULL && fn < rt->next_alloc && is_reducible(rt, fn)) {
                local_add_redex(w, fn);
            }
            if (arg != GIDX_NULL && arg < rt->next_alloc && is_reducible(rt, arg)) {
                local_add_redex(w, arg);
            }
            break;
        }
        case GTAG_DUP: {
            uint32_t target = soma_graph_deref(rt, n->data.pair.l);
            if (target != GIDX_NULL && target < rt->next_alloc && is_reducible(rt, target)) {
                local_add_redex(w, target);
            }
            break;
        }
        case GTAG_SUP: {
            uint32_t l = soma_graph_deref(rt, n->data.pair.l);
            uint32_t r = soma_graph_deref(rt, n->data.pair.r);
            if (l != GIDX_NULL && l < rt->next_alloc && is_reducible(rt, l)) {
                local_add_redex(w, l);
            }
            if (r != GIDX_NULL && r < rt->next_alloc && is_reducible(rt, r)) {
                local_add_redex(w, r);
            }
            break;
        }
        case GTAG_LAM: {
            uint32_t body = soma_graph_deref(rt, n->data.lam.body);
            if (body != GIDX_NULL && body < rt->next_alloc && is_reducible(rt, body)) {
                local_add_redex(w, body);
            }
            break;
        }
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            for (int i = 0; i < arity; i++) {
                uint32_t arg = soma_graph_deref(rt, get_call_arg(rt, n, i));
                if (arg != GIDX_NULL && arg < rt->next_alloc && is_reducible(rt, arg)) {
                    local_add_redex(w, arg);
                }
            }
            break;
        }
        default:
            break;
    }
}

/* Reduce a batch of nodes, writing new redexes to worker's LOCAL buffer */
static void reduce_batch(GraphRuntime* rt, GWorker* w, uint32_t start) {
    int cur = rt->current_buf;
    uint32_t count = atomic_load_explicit(&rt->redex_count_padded[cur].count, memory_order_relaxed);
    uint32_t end = start + BATCH_SIZE;
    if (end > count) end = count;
    
    for (uint32_t i = start; i < end; i++) {
        uint32_t idx = rt->redex_buf[cur][i];
        if (idx == GIDX_NULL) continue;
        
        int reduced = soma_graph_reduce_node(rt, idx);
        if (reduced) {
            w->reductions++;
        }
        
        GNode* n = &rt->nodes[idx];
        
        GDEBUG("  reduce_batch[%d]: idx=%u, reduced=%d, tag_after=0x%02x\n",
               w->id, idx, reduced, n->tag);
        
        /* If became IND (only happens when we reduced it), seed the new subgraph */
        if (reduced && n->tag == GTAG_IND) {
            uint32_t target = n->data.pair.l;
            GDEBUG("  reduce_batch[%d]: IND->%u, seeding target\n", w->id, target);
            if (target != GIDX_NULL && target < rt->next_alloc) {
                seed_redex_buf_local(rt, w, target);
            }
        }
        
        /* Check if this node is now a value (either we reduced it, or another worker did) */
        int is_now_value = soma_graph_is_value(rt, idx);
        
        /* Check parent - if node is a value OR an IND, parent might be reducible.
         * IMPORTANT: The parent might itself be an IND node (if a CALL became IND).
         * We need to follow IND chains upward to find a real reducible node. */
        if (is_now_value || n->tag == GTAG_IND) {
            uint32_t plink = atomic_load_explicit((_Atomic uint32_t*)&rt->parents[idx], memory_order_relaxed);
            GDEBUG("  reduce_batch[%d]: checking parent, plink=0x%08x\n", w->id, plink);
            
            /* Follow parent chain through IND nodes */
            int chain_limit = 100;
            while (plink != GIDX_NULL && chain_limit-- > 0) {
                uint32_t parent = PLINK_GET_INDEX(plink);
                if (parent >= rt->next_alloc) break;
                
                GNode* parent_node = &rt->nodes[parent];
                uint8_t parent_tag = atomic_load_explicit((_Atomic uint8_t*)&parent_node->tag, memory_order_relaxed);
                
                GDEBUG("  reduce_batch[%d]: parent=%u, tag=0x%02x\n", w->id, parent, parent_tag);
                
                if (parent_tag == GTAG_IND) {
                    /* Parent is an IND - follow up to its parent */
                    plink = atomic_load_explicit((_Atomic uint32_t*)&rt->parents[parent], memory_order_relaxed);
                    continue;
                }
                
                /* Found a non-IND parent - check if reducible */
                int parent_reducible = is_reducible(rt, parent);
                GDEBUG("  reduce_batch[%d]: parent=%u is non-IND, reducible=%d\n",
                       w->id, parent, parent_reducible);
                if (parent_reducible) {
                    local_add_redex_rt(rt, w, parent);
                }
                break;
            }
        }
        
        /* Periodic flush to prevent overflow */
        if (w->local_count >= (WORKER_LOCAL_BUF_SIZE * 3 / 4)) {
            flush_local_buffer(rt, w);
        }
    }
}

/* Flush worker's local buffer to next global buffer (called at barrier) */
static void flush_local_buffer(GraphRuntime* rt, GWorker* w) {
    if (w->local_count == 0) return;
    
    int next = 1 - rt->current_buf;
    /* Use release ordering so the memcpy is visible before the count increment */
    uint32_t start = atomic_fetch_add_explicit(&rt->redex_count_padded[next].count, 
                                                w->local_count, memory_order_release);
    
    /* Copy local buffer to global - one atomic for entire batch! */
    if (start + w->local_count <= GRAPH_REDEX_BUF_SIZE) {
        memcpy(&rt->redex_buf[next][start], w->local_buf, w->local_count * sizeof(uint32_t));
    }
    w->local_count = 0;
}

/* Barrier using futex for efficient waiting */
static void barrier_wait(GBarrier* b) {
    int gen = atomic_load_explicit(&b->generation, memory_order_acquire);
    if (atomic_fetch_add_explicit(&b->count, 1, memory_order_acq_rel) == b->num_threads - 1) {
        /* Last to arrive - reset and advance generation */
        atomic_store_explicit(&b->count, 0, memory_order_relaxed);
        atomic_fetch_add_explicit(&b->generation, 1, memory_order_release);
        /* Wake all waiters */
        futex_wake_all(&b->generation);
    } else {
        /* Wait for generation to advance using futex */
        futex_wait(&b->generation, gen);
    }
}

/* Worker thread function - HVM style with local buffers */
static void* worker_thread(void* arg) {
    GWorker* w = (GWorker*)arg;
    GraphRuntime* rt = g_graph_rt;
    uint64_t iterations = 0;
    
    GDEBUG("worker[%d]: started\n", w->id);
    
    while (!atomic_load_explicit(&rt->shutdown, memory_order_relaxed)) {
        int cur = rt->current_buf;
        uint32_t cur_count = atomic_load_explicit(&rt->redex_count_padded[cur].count, memory_order_relaxed);
        GDEBUG("worker[%d]: iter=%lu, cur_buf=%d, redex_count=%u\n", 
               w->id, (unsigned long)iterations, cur, cur_count);
        
        /* Grab and process batches until none left */
        uint32_t start;
        int batches_processed = 0;
        while ((start = grab_batch_start(rt)) != GIDX_NULL) {
            GDEBUG("worker[%d]: grabbed batch start=%u\n", w->id, start);
            reduce_batch(rt, w, start);
            batches_processed++;
        }
        GDEBUG("worker[%d]: processed %d batches, local_count=%u\n", 
               w->id, batches_processed, w->local_count);
        
        /* Flush local buffer to global BEFORE barrier */
        flush_local_buffer(rt, w);
        
        iterations++;
        
        /* Wait for all workers at barrier (ensures all flushes complete) */
        barrier_wait(&rt->barrier);
        
        /* Worker 0 swaps buffers and checks termination */
        if (w->id == 0) {
            int next = 1 - rt->current_buf;
            /* Use acquire to see all flushed data from other workers */
            uint32_t next_count = atomic_load_explicit(&rt->redex_count_padded[next].count, memory_order_acquire);
            uint32_t root_deref = soma_graph_deref(rt, rt->parallel_root);
            int is_val = soma_graph_is_value(rt, root_deref);
            
            GDEBUG("worker[0]: next_buf=%d, next_count=%u, root=%u, root_deref=%u, is_val=%d, root_tag=0x%02x\n",
                   next, next_count, rt->parallel_root, root_deref, is_val,
                   root_deref < rt->next_alloc ? rt->nodes[root_deref].tag : 0xFF);
            
            if (next_count == 0 || is_val) {
                GDEBUG("worker[0]: SHUTDOWN - next_count=%u, is_val=%d\n", next_count, is_val);
                atomic_store_explicit(&rt->shutdown, 1, memory_order_relaxed);
            } else {
                /* Swap buffers */
                rt->current_buf = next;
                atomic_store_explicit(&rt->redex_count_padded[1 - next].count, 0, memory_order_relaxed);
                atomic_store_explicit(&rt->next_redex_padded.value, 0, memory_order_relaxed);
            }
        }
        
        /* Second barrier to ensure swap is visible */
        barrier_wait(&rt->barrier);
    }
    
    GDEBUG("worker[%d]: exiting after %lu iterations, %lu reductions\n", 
           w->id, (unsigned long)iterations, (unsigned long)w->reductions);
    w->steals = iterations;  /* Reuse steals field for iteration count */
    atomic_fetch_add_explicit(&rt->workers_done, 1, memory_order_relaxed);
    return NULL;
}

/*
 * Task-Parallel Reduction - HVM3 style
 * 
 * Each worker independently reduces a subtree to completion.
 * Workers only communicate when stealing work from each other.
 * No barriers - pure task parallelism.
 * 
 * This is better for tree-structured computations like fib where
 * we want each worker to "own" a subtree.
 */

/* Helper: collect children of a node that need work */
static void collect_children(GraphRuntime* rt, uint32_t idx, uint32_t* out_nodes, int* out_count, int max_count) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return;
    uint32_t pool_limit = atomic_load_explicit(&rt->next_alloc, memory_order_relaxed);
    if (idx >= pool_limit) return;
    
    GNode* n = &rt->nodes[idx];
    
    /* Follow indirections with bounds checking and loop limit */
    int ind_limit = 1000;
    while (atomic_load_explicit((_Atomic uint8_t*)&n->tag, memory_order_relaxed) == GTAG_IND && ind_limit-- > 0) {
        idx = atomic_load_explicit((_Atomic uint32_t*)&n->data.pair.l, memory_order_relaxed);
        if (idx == GIDX_NULL || idx >= pool_limit) return;
        n = &rt->nodes[idx];
    }
    if (ind_limit <= 0) return;  /* Stuck in loop */
    
    switch (n->tag) {
        case GTAG_NUM:
        case GTAG_ERA:
            /* Values - nothing to collect */
            break;
            
        case GTAG_ADD: case GTAG_SUB: case GTAG_MUL: case GTAG_DIV: case GTAG_MOD:
        case GTAG_EQ: case GTAG_NE: case GTAG_LT: case GTAG_LE: case GTAG_GT: case GTAG_GE: {
            uint32_t l = soma_graph_deref(rt, n->data.pair.l);
            uint32_t r = soma_graph_deref(rt, n->data.pair.r);
            if (*out_count < max_count && !soma_graph_is_value(rt, l)) {
                out_nodes[(*out_count)++] = l;
            }
            if (*out_count < max_count && !soma_graph_is_value(rt, r)) {
                out_nodes[(*out_count)++] = r;
            }
            break;
        }
        case GTAG_APP: {
            uint32_t fn = soma_graph_deref(rt, n->data.pair.l);
            uint32_t arg = soma_graph_deref(rt, n->data.pair.r);
            if (*out_count < max_count && !soma_graph_is_value(rt, fn)) {
                out_nodes[(*out_count)++] = fn;
            }
            if (*out_count < max_count && !soma_graph_is_value(rt, arg)) {
                out_nodes[(*out_count)++] = arg;
            }
            break;
        }
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            /* Sanity check arity to handle corrupted/recycled nodes */
            if (arity < 0 || arity > 16) break;
            for (int i = 0; i < arity && *out_count < max_count; i++) {
                uint32_t arg = get_call_arg(rt, n, i);
                if (arg == GIDX_NULL || arg >= pool_limit) continue;
                arg = soma_graph_deref(rt, arg);
                if (arg != GIDX_NULL && arg < pool_limit && !soma_graph_is_value(rt, arg)) {
                    out_nodes[(*out_count)++] = arg;
                }
            }
            break;
        }
        case GTAG_DUP: {
            uint32_t target = soma_graph_deref(rt, n->data.pair.l);
            if (*out_count < max_count && !soma_graph_is_value(rt, target)) {
                out_nodes[(*out_count)++] = target;
            }
            break;
        }
        case GTAG_SUP: {
            uint32_t l = soma_graph_deref(rt, n->data.pair.l);
            uint32_t r = soma_graph_deref(rt, n->data.pair.r);
            if (*out_count < max_count && !soma_graph_is_value(rt, l)) {
                out_nodes[(*out_count)++] = l;
            }
            if (*out_count < max_count && !soma_graph_is_value(rt, r)) {
                out_nodes[(*out_count)++] = r;
            }
            break;
        }
        case GTAG_LAM: {
            uint32_t body = soma_graph_deref(rt, n->data.lam.body);
            if (*out_count < max_count && !soma_graph_is_value(rt, body)) {
                out_nodes[(*out_count)++] = body;
            }
            break;
        }
        default:
            break;
    }
}

/* Reduce a single node and return new nodes to process.
 * 
 * KEY: When a CALL is reduced, the function creates a NEW subgraph (e.g., 
 * graph_fib creates ADD(CALL, CALL)). We must return the CHILDREN of that 
 * new subgraph, not just the root, so workers can steal the independent work.
 */
static int reduce_and_collect(GraphRuntime* rt, uint32_t idx, uint32_t* out_nodes, int* out_count) {
    *out_count = 0;
    
    if (idx == GIDX_NULL || idx == GIDX_ERA) return 0;
    if (idx >= rt->next_alloc) return 0;
    
    GNode* n = &rt->nodes[idx];
    
    /* Follow indirections */
    while (n->tag == GTAG_IND) {
        idx = n->data.pair.l;
        if (idx == GIDX_NULL || idx >= rt->next_alloc) return 0;
        n = &rt->nodes[idx];
    }
    
    /* Already a value? */
    if (n->tag == GTAG_NUM || n->tag == GTAG_ERA) return 0;
    
    /* Try to reduce */
    if (is_reducible(rt, idx)) {
        int reduced = soma_graph_reduce_node(rt, idx);
        if (reduced) {
            n = &rt->nodes[idx];
            if (n->tag == GTAG_IND) {
                /* CALL was reduced - collect children of the NEW subgraph!
                 * 
                 * Example: CALL(fib, 25) -> IND -> ADD(CALL(fib,24), CALL(fib,23))
                 * We want to return BOTH child CALLs so they can be stolen. */
                uint32_t target = n->data.pair.l;
                if (target != GIDX_NULL && target < rt->next_alloc) {
                    /* Collect children of the target (the new subgraph root) */
                    collect_children(rt, target, out_nodes, out_count, 8);
                    
                    /* If no children collected, return the target itself */
                    if (*out_count == 0) {
                        out_nodes[(*out_count)++] = target;
                    }
                }
            }
            return 1;
        }
    }
    
    /* Not reducible - collect children that need work */
    collect_children(rt, idx, out_nodes, out_count, 8);
    
    return 0;
}

/* Worker local stack for DFS traversal */
#define LOCAL_STACK_SIZE 4096

/* Push a task to the global work queue for stealing */
static inline void spawn_task(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA || idx >= rt->next_alloc) return;
    uint32_t pos = atomic_fetch_add_explicit(&rt->redex_count_padded[0].count, 1, memory_order_release);
    if (pos < GRAPH_REDEX_BUF_SIZE) {
        rt->redex_buf[0][pos] = idx;
    }
}

/* Try to steal a task from the global work queue */
static inline uint32_t steal_task(GraphRuntime* rt) {
    uint32_t cur_count = atomic_load_explicit(&rt->redex_count_padded[0].count, memory_order_acquire);
    uint32_t cur_next = atomic_load_explicit(&rt->next_redex_padded.value, memory_order_relaxed);
    if (cur_next < cur_count) {
        uint32_t start = atomic_fetch_add_explicit(&rt->next_redex_padded.value, 1, memory_order_acq_rel);
        if (start < cur_count) {
            return rt->redex_buf[0][start];
        }
    }
    return GIDX_NULL;
}

/*
 * Fully reduce a subtree to a value, using local stack only (no spawning).
 * Returns 1 if reduced to value, 0 if stuck.
 */
static int reduce_subtree_local(GraphRuntime* rt, GWorker* w, uint32_t root) {
    uint32_t stack[4096];
    int stack_top = 0;
    
    stack[stack_top++] = root;
    
    while (stack_top > 0) {
        uint32_t idx = stack[--stack_top];
        
        if (idx == GIDX_NULL || idx == GIDX_ERA) continue;
        if (idx >= rt->next_alloc) continue;
        
        /* Follow indirections */
        idx = soma_graph_deref(rt, idx);
        if (idx == GIDX_NULL || idx == GIDX_ERA || idx >= rt->next_alloc) continue;
        
        GNode* n = &rt->nodes[idx];
        uint8_t tag = n->tag;
        
        /* Already a value? */
        if (tag == GTAG_NUM || tag == GTAG_ERA) continue;
        
        /* Try to reduce */
        if (is_reducible(rt, idx)) {
            if (soma_graph_reduce_node(rt, idx)) {
                w->reductions++;
                n = &rt->nodes[idx];
                
                if (n->tag == GTAG_IND) {
                    /* Push the new target */
                    if (stack_top < 4090) {
                        stack[stack_top++] = n->data.pair.l;
                    }
                }
            }
            continue;
        }
        
        /* Not reducible - push children and self */
        uint32_t children[8];
        int child_count = 0;
        collect_children(rt, idx, children, &child_count, 8);
        
        if (child_count > 0 && stack_top < 4090 - child_count - 1) {
            stack[stack_top++] = idx;  /* Re-check after children */
            for (int i = 0; i < child_count; i++) {
                stack[stack_top++] = children[i];
            }
        }
    }
    
    return soma_graph_is_value(rt, soma_graph_deref(rt, root));
}

/*
 * Task-parallel worker - coarse-grained work stealing.
 * 
 * Key insight: Only spawn CALL nodes at the first level of recursion.
 * Once a worker owns a subtree, it reduces it completely locally.
 * This minimizes atomic operations and maximizes cache locality.
 */
static void* task_worker_thread(void* arg) {
    GWorker* w = (GWorker*)arg;
    GraphRuntime* rt = g_graph_rt;
    
    uint64_t idle_spins = 0;
    const uint64_t MAX_IDLE_SPINS = 100000;
    
    /* Worker 0 seeds the initial work by finding all top-level CALL nodes */
    if (w->id == 0) {
        /* Find all CALL nodes in the tree and spawn them as independent tasks.
         * This gives each worker a whole fib(N) subtree to reduce. */
        uint32_t seed_stack[256];
        int seed_top = 0;
        seed_stack[seed_top++] = rt->parallel_root;
        
        while (seed_top > 0) {
            uint32_t idx = seed_stack[--seed_top];
            if (idx == GIDX_NULL || idx == GIDX_ERA || idx >= rt->next_alloc) continue;
            
            idx = soma_graph_deref(rt, idx);
            if (idx == GIDX_NULL || idx == GIDX_ERA || idx >= rt->next_alloc) continue;
            
            GNode* n = &rt->nodes[idx];
            
            if (n->tag == GTAG_CALL) {
                /* Found a CALL - spawn it as a task */
                spawn_task(rt, idx);
            } else if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL ||
                       n->tag == GTAG_SUP) {
                /* Binary node - recurse into children */
                if (seed_top < 254) {
                    seed_stack[seed_top++] = n->data.pair.l;
                    seed_stack[seed_top++] = n->data.pair.r;
                }
            }
            /* Ignore NUM, ERA, IND (values) */
        }
        
        /* Also spawn the root to be finalized after all CALLs complete */
        spawn_task(rt, rt->parallel_root);
    }
    
    /* Small delay to let worker 0 finish seeding before others start stealing */
    if (w->id != 0) {
        for (volatile int i = 0; i < 1000; i++) {}
    }
    
    while (!atomic_load_explicit(&rt->shutdown, memory_order_relaxed)) {
        /* Try to steal a task */
        uint32_t task = steal_task(rt);
        
        if (task != GIDX_NULL && task < rt->next_alloc) {
            w->steals++;
            idle_spins = 0;
            
            /* Reduce this entire subtree locally */
            reduce_subtree_local(rt, w, task);
            
            /* After reducing, check if it created new parallelizable work.
             * If the task was a CALL that created an ADD(CALL, CALL),
             * spawn the CALL children for other workers. */
            uint32_t result = soma_graph_deref(rt, task);
            if (result != GIDX_NULL && result < rt->next_alloc) {
                GNode* n = &rt->nodes[result];
                if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
                    /* Check if children are CALLs (not yet reduced) */
                    uint32_t l = soma_graph_deref(rt, n->data.pair.l);
                    uint32_t r = soma_graph_deref(rt, n->data.pair.r);
                    
                    if (l < rt->next_alloc && rt->nodes[l].tag == GTAG_CALL) {
                        spawn_task(rt, l);
                    }
                    if (r < rt->next_alloc && rt->nodes[r].tag == GTAG_CALL) {
                        spawn_task(rt, r);
                    }
                    
                    /* Re-spawn this node to be reduced after children */
                    if (!soma_graph_is_value(rt, result)) {
                        spawn_task(rt, result);
                    }
                }
            }
            continue;
        }
        
        /* No work available */
        idle_spins++;
        
        if (idle_spins > MAX_IDLE_SPINS) {
            /* Check if we're done */
            uint32_t root_deref = soma_graph_deref(rt, rt->parallel_root);
            if (soma_graph_is_value(rt, root_deref)) {
                atomic_store_explicit(&rt->shutdown, 1, memory_order_release);
                break;
            }
            
            /* Worker 0 re-seeds if stuck */
            if (w->id == 0) {
                spawn_task(rt, rt->parallel_root);
            }
            idle_spins = 0;
        }
        
        /* Yield to avoid spinning */
        sched_yield();
    }
    
    atomic_fetch_add_explicit(&rt->workers_done, 1, memory_order_relaxed);
    return NULL;
}

/* Task-parallel reduction entry point */
int64_t soma_graph_reduce_taskpar(GraphRuntime* rt, uint32_t root) {
    if (root == GIDX_NULL || root == GIDX_ERA) return 0;
    
    /* If single-threaded mode, use fast reducer */
    if (rt->num_workers <= 1) {
        return soma_graph_reduce_fast(rt, root);
    }
    
    /* Reset state */
    atomic_store(&rt->shutdown, 0);
    atomic_store(&rt->workers_done, 0);
    atomic_store(&rt->redex_count_padded[0].count, 0);
    atomic_store(&rt->redex_count_padded[1].count, 0);
    atomic_store(&rt->next_redex_padded.value, 0);
    rt->current_buf = 0;
    rt->parallel_root = root;
    
    /* Initialize workers */
    for (int i = 0; i < rt->num_workers; i++) {
        rt->workers[i].id = i;
        rt->workers[i].reductions = 0;
        rt->workers[i].steals = 0;
        atomic_store(&rt->workers[i].active, 1);
    }
    
    /* Spawn worker threads */
    for (int i = 1; i < rt->num_workers; i++) {
        pthread_create(&rt->workers[i].thread, NULL, task_worker_thread, &rt->workers[i]);
    }
    
    /* Main thread also runs as worker 0 */
    task_worker_thread(&rt->workers[0]);
    
    /* Wait for other workers */
    for (int i = 1; i < rt->num_workers; i++) {
        pthread_join(rt->workers[i].thread, NULL);
    }
    
    /* Collect statistics */
    uint64_t total_reductions = 0;
    for (int i = 0; i < rt->num_workers; i++) {
        total_reductions += rt->workers[i].reductions;
    }
    atomic_store(&rt->total_reductions, total_reductions);
    
    /* Follow indirections to get final value */
    uint32_t final_idx = soma_graph_deref(rt, root);
    if (soma_graph_is_value(rt, final_idx)) {
        return rt->nodes[final_idx].data.num;
    }
    
    fprintf(stderr, "soma_graph_reduce_taskpar: failed to reduce to value\n");
    return 0;
}

/* Seed redex buffer with initial reducible nodes */
static void seed_redex_buf(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return;
    if (idx >= rt->next_alloc) return;
    
    GNode* n = &rt->nodes[idx];
    
    if (n->tag == GTAG_IND) {
        seed_redex_buf(rt, n->data.pair.l);
        return;
    }
    
    uint8_t status = atomic_load((_Atomic uint8_t*)&n->status);
    if (status == GSTAT_DONE || status == GSTAT_REDUCING) return;
    
    if (is_reducible(rt, idx)) {
        uint32_t pos = atomic_fetch_add(&rt->redex_count_padded[0].count, 1);
        if (pos < GRAPH_REDEX_BUF_SIZE) {
            rt->redex_buf[0][pos] = idx;
        }
        return;
    }
    
    switch (n->tag) {
        case GTAG_ADD: case GTAG_SUB: case GTAG_MUL: case GTAG_DIV: case GTAG_MOD:
        case GTAG_EQ: case GTAG_NE: case GTAG_LT: case GTAG_LE: case GTAG_GT: case GTAG_GE:
            seed_redex_buf(rt, n->data.pair.l);
            seed_redex_buf(rt, n->data.pair.r);
            break;
        case GTAG_APP:
            seed_redex_buf(rt, n->data.pair.l);
            seed_redex_buf(rt, n->data.pair.r);
            break;
        case GTAG_DUP:
            seed_redex_buf(rt, n->data.pair.l);
            break;
        case GTAG_SUP:
            seed_redex_buf(rt, n->data.pair.l);
            seed_redex_buf(rt, n->data.pair.r);
            break;
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            for (int i = 0; i < arity; i++)
                seed_redex_buf(rt, get_call_arg(rt, n, i));
            break;
        }
        case GTAG_LAM:
            seed_redex_buf(rt, n->data.lam.body);
            break;
        default:
            break;
    }
}

/* Parallel reduction - HVM style */
int64_t soma_graph_reduce_parallel(GraphRuntime* rt, uint32_t root) {
    if (root == GIDX_NULL || root == GIDX_ERA) return 0;
    
    GDEBUG("reduce_parallel: root=%u, num_workers=%d\n", root, rt->num_workers);
    
    /* If single-threaded mode, use fast reducer */
    if (rt->num_workers <= 1) {
        return soma_graph_reduce_fast(rt, root);
    }
    
    /* Reset state */
    atomic_store(&rt->shutdown, 0);
    atomic_store(&rt->workers_done, 0);
    atomic_store(&rt->redex_count_padded[0].count, 0);
    atomic_store(&rt->redex_count_padded[1].count, 0);
    atomic_store(&rt->next_redex_padded.value, 0);
    rt->current_buf = 0;
    rt->parallel_root = root;
    
    /* Initialize barrier */
    rt->barrier.num_threads = rt->num_workers;
    atomic_store(&rt->barrier.count, 0);
    atomic_store(&rt->barrier.generation, 0);
    
    /* Initialize workers */
    for (int i = 0; i < rt->num_workers; i++) {
        rt->workers[i].id = i;
        rt->workers[i].reductions = 0;
        rt->workers[i].steals = 0;
        atomic_store(&rt->workers[i].active, 1);
    }
    
    /* Seed initial redexes */
    seed_redex_buf(rt, root);
    GDEBUG("reduce_parallel: seeded %lu redexes\n", 
           (unsigned long)atomic_load(&rt->redex_count_padded[0].count));
    
    /* Spawn worker threads (all workers including 0) */
    for (int i = 1; i < rt->num_workers; i++) {
        pthread_create(&rt->workers[i].thread, NULL, worker_thread, &rt->workers[i]);
    }
    
    /* Main thread also runs as worker 0 */
    worker_thread(&rt->workers[0]);
    
    /* Wait for other workers */
    for (int i = 1; i < rt->num_workers; i++) {
        pthread_join(rt->workers[i].thread, NULL);
    }
    
    /* Collect statistics */
    uint64_t total_reductions = 0;
    for (int i = 0; i < rt->num_workers; i++) {
        total_reductions += rt->workers[i].reductions;
    }
    atomic_store(&rt->total_reductions, total_reductions);
    
    /* Follow indirections to get final value */
    uint32_t final_idx = soma_graph_deref(rt, root);
    if (soma_graph_is_value(rt, final_idx)) {
        return rt->nodes[final_idx].data.num;
    }
    
    fprintf(stderr, "soma_graph_reduce_parallel: failed to reduce to value\n");
    return 0;
}

/*
 * Debugging
 */

static const char* tag_name(uint8_t tag) {
    switch (tag) {
        case GTAG_NUM: return "NUM";
        case GTAG_ERA: return "ERA";
        case GTAG_ADD: return "ADD";
        case GTAG_SUB: return "SUB";
        case GTAG_MUL: return "MUL";
        case GTAG_DIV: return "DIV";
        case GTAG_MOD: return "MOD";
        case GTAG_EQ:  return "EQ";
        case GTAG_NE:  return "NE";
        case GTAG_LT:  return "LT";
        case GTAG_LE:  return "LE";
        case GTAG_GT:  return "GT";
        case GTAG_GE:  return "GE";
        case GTAG_CALL: return "CALL";
        case GTAG_APP: return "APP";
        case GTAG_LAM: return "LAM";
        case GTAG_REF: return "REF";
        case GTAG_SUP: return "SUP";
        case GTAG_DUP: return "DUP";
        case GTAG_CON: return "CON";
        case GTAG_IND: return "IND";
        default: return "???";
    }
}

void soma_graph_print_node(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL) {
        fprintf(stderr, "NULL");
        return;
    }
    if (idx == GIDX_ERA) {
        fprintf(stderr, "ERA");
        return;
    }
    if (idx >= rt->next_alloc) {
        fprintf(stderr, "INVALID(%u)", idx);
        return;
    }
    
    GNode* n = &rt->nodes[idx];
    fprintf(stderr, "%s@%u", tag_name(n->tag), idx);
    
    switch (n->tag) {
        case GTAG_NUM:
            fprintf(stderr, "(%ld)", n->data.num);
            break;
        case GTAG_ADD:
        case GTAG_SUB:
        case GTAG_MUL:
        case GTAG_APP:
        case GTAG_SUP:
            fprintf(stderr, "(%u,%u)", n->data.pair.l, n->data.pair.r);
            break;
        case GTAG_CALL:
            fprintf(stderr, "(fn=%u,arity=%u)", n->data.call.fn, n->data.call.arity);
            break;
        default:
            break;
    }
}

void soma_graph_print_stats(GraphRuntime* rt) {
    uint64_t fresh_alloc = atomic_load(&rt->next_alloc) - 1;  /* -1 for reserved slot 0 */
    uint64_t recycled = atomic_load(&rt->nodes_recycled);
    uint64_t reused = atomic_load(&rt->nodes_reused);
    uint64_t total_allocs = fresh_alloc + reused;
    fprintf(stderr, "\n=== Graph Runtime Statistics ===\n");
    fprintf(stderr, "Fresh allocations: %lu / %u\n", fresh_alloc, rt->pool_size);
    fprintf(stderr, "Nodes recycled: %lu\n", recycled);
    fprintf(stderr, "Nodes reused: %lu\n", reused);
    fprintf(stderr, "Total allocations: %lu (%.1f%% reused)\n", 
            total_allocs, total_allocs > 0 ? (100.0 * reused / total_allocs) : 0.0);
    fprintf(stderr, "Total reductions: %lu\n", 
            atomic_load(&rt->total_reductions));
    fprintf(stderr, "Wavefront iterations: %lu\n", 
            atomic_load(&rt->wavefront_iterations));
    fprintf(stderr, "================================\n");
}

void soma_graph_dump(GraphRuntime* rt, uint32_t root, int max_depth) {
    /* Simple recursive dump with depth limit */
    if (max_depth <= 0) {
        fprintf(stderr, "...");
        return;
    }
    if (root == GIDX_NULL) {
        fprintf(stderr, "NULL");
        return;
    }
    if (root == GIDX_ERA) {
        fprintf(stderr, "*");
        return;
    }
    if (root >= rt->next_alloc) {
        fprintf(stderr, "INVALID");
        return;
    }
    
    GNode* n = &rt->nodes[root];
    
    switch (n->tag) {
        case GTAG_NUM:
            fprintf(stderr, "%ld", n->data.num);
            break;
        case GTAG_ERA:
            fprintf(stderr, "*");
            break;
        case GTAG_ADD:
            fprintf(stderr, "(");
            soma_graph_dump(rt, n->data.pair.l, max_depth - 1);
            fprintf(stderr, " + ");
            soma_graph_dump(rt, n->data.pair.r, max_depth - 1);
            fprintf(stderr, ")");
            break;
        case GTAG_SUB:
            fprintf(stderr, "(");
            soma_graph_dump(rt, n->data.pair.l, max_depth - 1);
            fprintf(stderr, " - ");
            soma_graph_dump(rt, n->data.pair.r, max_depth - 1);
            fprintf(stderr, ")");
            break;
        case GTAG_MUL:
            fprintf(stderr, "(");
            soma_graph_dump(rt, n->data.pair.l, max_depth - 1);
            fprintf(stderr, " * ");
            soma_graph_dump(rt, n->data.pair.r, max_depth - 1);
            fprintf(stderr, ")");
            break;
        case GTAG_CALL: {
            GFunc* fn = soma_graph_get_func(rt, n->data.call.fn);
            fprintf(stderr, "%s(", fn ? fn->name : "?");
            for (int i = 0; i < n->data.call.arity; i++) {
                if (i > 0) fprintf(stderr, ", ");
                soma_graph_dump(rt, get_call_arg(rt, n, i), max_depth - 1);
            }
            fprintf(stderr, ")");
            break;
        }
        default:
            fprintf(stderr, "%s@%u", tag_name(n->tag), root);
            break;
    }
}

/*
 * Fork-Join Parallel Reduction
 * 
 * This approach achieves true parallelism by giving each worker its own
 * GraphRuntime. This eliminates all contention on:
 *   - Node allocation (atomic next_alloc)
 *   - Parent pointer updates
 *   - Work queues
 *
 * The algorithm:
 * 1. Collect top-level CALL nodes from the expression tree
 * 2. Spawn worker threads, each with its own runtime
 * 3. Each worker reduces its assigned CALLs independently
 * 4. Main thread collects results and replaces CALLs with NUMs
 * 5. Final single-threaded reduction of the remaining ADD tree
 *
 * This is optimal for expressions like: fib(25) + fib(25) + fib(25) + ...
 * where each fib(25) is completely independent.
 */

#define FORKJOIN_MAX_TASKS 256

typedef struct ForkJoinTask {
    int task_id;
    int64_t arg_value;           /* The argument to the CALL (e.g., n for fib(n)) */
    uint16_t func_idx;           /* Function index */
    int64_t result;              /* Result after reduction */
    GraphRuntime* parent_rt;     /* Parent runtime (for copying function table) */
} ForkJoinTask;

/* Worker thread for fork-join: creates its own runtime and reduces a single CALL */
static void* forkjoin_worker(void* arg) {
    ForkJoinTask* task = (ForkJoinTask*)arg;
    
    /* Create a fresh runtime for this worker */
    GraphRuntime* rt = soma_graph_init(0);
    if (!rt) {
        task->result = 0;
        return NULL;
    }
    
    /* Copy the function table from the parent runtime */
    GraphRuntime* parent = task->parent_rt;
    for (uint32_t i = 0; i < parent->num_functions; i++) {
        GFunc* fn = &parent->functions[i];
        soma_graph_register_func(rt, fn->name, fn->arity, fn->flags, fn->impl);
    }
    
    /* Build and reduce: CALL(func_idx, arg_value) */
    uint32_t arg_node = soma_graph_num(rt, task->arg_value);
    uint32_t call_node = soma_graph_call1(rt, task->func_idx, arg_node);
    
    task->result = soma_graph_reduce_fast(rt, call_node);
    
    soma_graph_shutdown(rt);
    return NULL;
}

/* Collect CALL nodes from the tree up to max_tasks */
static int collect_calls(GraphRuntime* rt, uint32_t root, 
                         uint32_t* call_indices, int64_t* call_args, 
                         uint16_t* call_funcs, int max_tasks) {
    int count = 0;
    uint32_t stack[1024];
    int stack_top = 0;
    
    stack[stack_top++] = root;
    
    while (stack_top > 0 && count < max_tasks) {
        uint32_t idx = stack[--stack_top];
        if (idx == GIDX_NULL || idx == GIDX_ERA || idx >= rt->next_alloc) continue;
        
        GNode* n = &rt->nodes[idx];
        
        /* Follow indirections */
        while (n->tag == GTAG_IND) {
            idx = n->data.pair.l;
            if (idx == GIDX_NULL || idx >= rt->next_alloc) goto next_iter;
            n = &rt->nodes[idx];
        }
        
        if (n->tag == GTAG_CALL && n->data.call.arity == 1) {
            /* Found a unary CALL - check if arg is a NUM */
            uint32_t arg_idx = get_call_arg(rt, n, 0);
            arg_idx = soma_graph_deref(rt, arg_idx);
            if (arg_idx < rt->next_alloc && rt->nodes[arg_idx].tag == GTAG_NUM) {
                call_indices[count] = idx;
                call_args[count] = rt->nodes[arg_idx].data.num;
                call_funcs[count] = n->data.call.fn;
                count++;
            }
        } else if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
            /* Binary op - recurse into children */
            if (stack_top < 1022) {
                stack[stack_top++] = n->data.pair.l;
                stack[stack_top++] = n->data.pair.r;
            }
        }
        /* Ignore NUM, ERA, and other nodes */
        
        next_iter:;
    }
    
    return count;
}

/* Fork-join parallel reduction */
int64_t soma_graph_reduce_forkjoin(GraphRuntime* rt, uint32_t root) {
    if (root == GIDX_NULL || root == GIDX_ERA) return 0;
    
    /* If single-threaded mode or small tree, use fast reducer */
    if (rt->num_workers <= 1) {
        return soma_graph_reduce_fast(rt, root);
    }
    
    /* Collect CALL nodes that can be parallelized */
    uint32_t call_indices[FORKJOIN_MAX_TASKS];
    int64_t call_args[FORKJOIN_MAX_TASKS];
    uint16_t call_funcs[FORKJOIN_MAX_TASKS];
    
    int num_calls = collect_calls(rt, root, call_indices, call_args, call_funcs, FORKJOIN_MAX_TASKS);
    
    GDEBUG("forkjoin: found %d CALL nodes to parallelize\n", num_calls);
    
    /* If not enough parallelism, fall back to single-threaded */
    if (num_calls < 2) {
        return soma_graph_reduce_fast(rt, root);
    }
    
    /* Limit workers to number of tasks */
    int num_workers = rt->num_workers;
    if (num_workers > num_calls) num_workers = num_calls;
    
    /* Create tasks - distribute calls among workers */
    ForkJoinTask* tasks = calloc(num_calls, sizeof(ForkJoinTask));
    pthread_t* threads = calloc(num_workers, sizeof(pthread_t));
    
    if (!tasks || !threads) {
        free(tasks);
        free(threads);
        return soma_graph_reduce_fast(rt, root);
    }
    
    for (int i = 0; i < num_calls; i++) {
        tasks[i].task_id = i;
        tasks[i].arg_value = call_args[i];
        tasks[i].func_idx = call_funcs[i];
        tasks[i].result = 0;
        tasks[i].parent_rt = rt;
    }
    
    /* Process tasks in batches of num_workers */
    int task_idx = 0;
    while (task_idx < num_calls) {
        int batch_size = (num_calls - task_idx < num_workers) ? (num_calls - task_idx) : num_workers;
        
        /* Start worker threads for this batch */
        for (int t = 0; t < batch_size; t++) {
            pthread_create(&threads[t], NULL, forkjoin_worker, &tasks[task_idx + t]);
        }
        
        /* Wait for batch to complete */
        for (int t = 0; t < batch_size; t++) {
            pthread_join(threads[t], NULL);
        }
        
        task_idx += batch_size;
    }
    
    /* Replace CALL nodes with their computed results (as NUM nodes) */
    for (int i = 0; i < num_calls; i++) {
        uint32_t idx = call_indices[i];
        GNode* n = &rt->nodes[idx];
        
        /* Convert CALL to NUM with the computed result */
        n->tag = GTAG_NUM;
        n->status = GSTAT_DONE;
        n->data.num = tasks[i].result;
    }
    
    free(tasks);
    free(threads);
    
    /* Final reduction of the ADD tree (now all children are NUMs) */
    return soma_graph_reduce_fast(rt, root);
}
