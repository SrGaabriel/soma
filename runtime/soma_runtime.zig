const std = @import("std");
const builtin = @import("builtin");

pub const panic = std.debug.no_panic;

const opts = @import("soma_runtime_options");

const pool_stats_enabled: bool = opts.pool_stats;

pub const SOMA_CACHELINE: comptime_int = 64;

pub const NODE_CLOSURE: u8 = 1;
pub const NODE_FLAT_ARRAY: u8 = 4;
pub const NODE_FLAT_ARRAY_VIEW: u8 = 5;

pub const SUP_TAG_FRESH: u8 = 0x80;
pub const SUP_TAG_PROJ0: u8 = 0x81;
pub const SUP_TAG_PROJ1: u8 = 0x82;
pub const SUP_TAG_BOTH: u8 = 0x83;
pub const SUP_TAG_PROJ0_CLONING: u8 = 0x84;
pub const SUP_TAG_PROJ1_CLONING: u8 = 0x85;

inline fn isSup(tag: u8) bool {
    return (tag & 0x80) != 0;
}

pub const SOMA_SUP_PAD0: u8 = 'S';
pub const SOMA_SUP_PAD1: u8 = 'U';
pub const SOMA_SUP_PAD2: u8 = 'P';

const SOMA_SUP_HEADER_FRESH: u32 =
    @as(u32, SUP_TAG_FRESH) |
    (@as(u32, SOMA_SUP_PAD0) << 8) |
    (@as(u32, SOMA_SUP_PAD1) << 16) |
    (@as(u32, SOMA_SUP_PAD2) << 24);

const SOMA_SUP_MAGIC_U32: u32 =
    (@as(u32, SOMA_SUP_PAD2) << 16) |
    (@as(u32, SOMA_SUP_PAD1) << 8) |
    @as(u32, SOMA_SUP_PAD0);

const ptr_width_bits: comptime_int = @bitSizeOf(usize);
const is_64bit: bool = ptr_width_bits == 64;
pub const TAG_BITS: u6 = if (is_64bit) 3 else 2;
pub const TAG_MASK: usize = (@as(usize, 1) << TAG_BITS) - 1;
pub const PAYLOAD_SHIFT: u6 = TAG_BITS;

pub const TAG_PTR: usize = 0;
pub const TAG_INT: usize = 1;
pub const TAG_BOOL: usize = 2;
pub const TAG_CHAR: usize = 3;

pub const BOOL_FALSE: usize = 0;
pub const BOOL_TRUE: usize = 1;
pub const BOOL_UNIT: usize = 2;

pub const SomaValue = usize;

inline fn getTag(v: SomaValue) usize {
    return v & TAG_MASK;
}

inline fn isPtr(v: SomaValue) bool {
    return getTag(v) == TAG_PTR;
}

inline fn toPtr(v: SomaValue) ?*anyopaque {
    return @ptrFromInt(v);
}

pub const SomaCloneFn = *const fn (value: ?*anyopaque, label: u32) callconv(.c) ?*anyopaque;
pub const SomaEraseFn = *const fn (value: ?*anyopaque) callconv(.c) void;

pub const SomaTypeDesc = extern struct {
    clone_fn: SomaCloneFn,
    erase_fn: SomaEraseFn,
};

pub const SomaClosure = extern struct {
    arity: u8,
    _pad: [@sizeOf(usize) - 1]u8,
    func_ptr: ?*anyopaque,
};

pub const SomaSup = extern struct {
    tag: u8,
    _pad: [3]u8,
    label: u32,
    value: ?*anyopaque,
    proj0: ?*anyopaque,
    proj1: ?*anyopaque,
    type_desc: ?*SomaTypeDesc,
};

pub const SomaString = extern struct {
    data: ?[*]u8,
    len: i64,
};

pub const SomaFlatArray = extern struct {
    tag: u8,
    elem_size: u8,
    _pad: [2]u8,
    _reserved: u32,
    length: i64,
};

pub const SomaFlatArrayView = extern struct {
    tag: u8,
    _pad: [3]u8,
    _reserved: u32,
    length: i64,
    data: ?*anyopaque,
    backing: ?*anyopaque,
};

pub const SomaList = extern struct {
    data: ?*anyopaque,
    len: u32,
    offset: u32,
};

const SOMA_LIST_NIL: SomaList = .{ .data = null, .len = 0, .offset = 0 };

const SOMA_STRING_STATIC_BIT: i64 = @bitCast(@as(u64, 1) << 63);

inline fn somaStringLen(s: SomaString) i64 {
    return s.len & ~SOMA_STRING_STATIC_BIT;
}

const SomaBoxedList = extern struct {
    data: ?*anyopaque,
    len: u32,
    offset: u32,
    elem_size: u16,
};

pub const SomaPoolBlock = extern struct {
    next: ?*SomaPoolBlock,
    used: u32,
    _pad: u32,
};

pub const POOL_BLOCK_SIZE: usize = 256 * 1024;
pub const POOL_SIZE_48: usize = 48;
pub const POOL_SIZE_112: usize = 112;

pub const SomaPool = extern struct {
    bump_ptr: ?[*]u8,
    bump_limit: ?[*]u8,
    free_list: ?*anyopaque,
    item_size: usize,
    blocks: ?*SomaPoolBlock,
};

pub const SomaPools = extern struct {
    pool_48: SomaPool align(SOMA_CACHELINE),
    pool_112: SomaPool align(SOMA_CACHELINE),
};

comptime {
    if (is_64bit) {
        std.debug.assert(@sizeOf(SomaClosure) == 16);
        std.debug.assert(@sizeOf(SomaSup) == 40 or @sizeOf(SomaSup) == 48);
        std.debug.assert(@sizeOf(SomaFlatArrayView) == 32);
        std.debug.assert(@sizeOf(SomaFlatArray) == 16);
        std.debug.assert(@sizeOf(SomaList) == 16);
    } else {
        std.debug.assert(@sizeOf(SomaClosure) == 8);
        std.debug.assert(@sizeOf(SomaSup) <= 28);
        std.debug.assert(@sizeOf(SomaList) == 12);
    }
    std.debug.assert(@sizeOf(SomaSup) <= POOL_SIZE_48);
    std.debug.assert(@sizeOf(SomaFlatArrayView) <= POOL_SIZE_48);
}

extern "c" fn malloc(size: usize) ?*anyopaque;
extern "c" fn realloc(ptr: ?*anyopaque, size: usize) ?*anyopaque;
extern "c" fn free(ptr: ?*anyopaque) void;
extern "c" fn memcpy(dst: ?*anyopaque, src: ?*const anyopaque, n: usize) ?*anyopaque;
extern "c" fn memset(dst: ?*anyopaque, c: c_int, n: usize) ?*anyopaque;
extern "c" fn strlen(s: [*:0]const u8) usize;
extern "c" fn exit(status: c_int) noreturn;

const is_windows: bool = builtin.os.tag == .windows;

extern "c" fn _aligned_malloc(size: usize, alignment: usize) ?*anyopaque;
extern "c" fn _aligned_free(ptr: ?*anyopaque) void;
extern "c" fn posix_memalign(memptr: *?*anyopaque, alignment: usize, size: usize) c_int;

fn somaAlignedAlloc(alignment: usize, size: usize) ?*anyopaque {
    if (is_windows) {
        return _aligned_malloc(size, alignment);
    }
    var ptr: ?*anyopaque = null;
    if (posix_memalign(&ptr, alignment, size) != 0) return null;
    return ptr;
}

fn somaAlignedFree(ptr: ?*anyopaque) void {
    if (is_windows) {
        _aligned_free(ptr);
    } else {
        free(ptr);
    }
}

extern "c" fn write(fd: c_int, buf: [*]const u8, count: usize) isize;

const win = if (is_windows) struct {
    pub const HANDLE = *anyopaque;
    pub const STD_ERROR_HANDLE: u32 = @bitCast(@as(i32, -12));
    pub extern "kernel32" fn GetStdHandle(nStdHandle: u32) callconv(.winapi) ?HANDLE;
    pub extern "kernel32" fn WriteFile(
        hFile: HANDLE,
        lpBuffer: [*]const u8,
        nNumberOfBytesToWrite: u32,
        lpNumberOfBytesWritten: ?*u32,
        lpOverlapped: ?*anyopaque,
    ) callconv(.winapi) c_int;
} else struct {};

fn writeStderr(bytes: []const u8) void {
    if (is_windows) {
        const h = win.GetStdHandle(win.STD_ERROR_HANDLE) orelse return;
        var written: u32 = 0;
        _ = win.WriteFile(h, bytes.ptr, @intCast(bytes.len), &written, null);
    } else {
        _ = write(2, bytes.ptr, bytes.len);
    }
}

const SomaPoolStats = extern struct {
    sup_allocs: std.atomic.Value(usize) = .{ .raw = 0 },
    sup_frees: std.atomic.Value(usize) = .{ .raw = 0 },
    small_allocs: std.atomic.Value(usize) = .{ .raw = 0 },
    small_frees: std.atomic.Value(usize) = .{ .raw = 0 },
    medium_allocs: std.atomic.Value(usize) = .{ .raw = 0 },
    medium_frees: std.atomic.Value(usize) = .{ .raw = 0 },
    large_allocs: std.atomic.Value(usize) = .{ .raw = 0 },
    large_frees: std.atomic.Value(usize) = .{ .raw = 0 },
    blocks_allocated: std.atomic.Value(usize) = .{ .raw = 0 },
    bytes_allocated: std.atomic.Value(usize) = .{ .raw = 0 },
};

var soma_pool_stats_storage: SomaPoolStats = .{};

inline fn statInc(comptime field: []const u8) void {
    if (comptime pool_stats_enabled) {
        _ = @field(soma_pool_stats_storage, field).fetchAdd(1, .monotonic);
    }
}

inline fn statAdd(comptime field: []const u8, n: usize) void {
    if (comptime pool_stats_enabled) {
        _ = @field(soma_pool_stats_storage, field).fetchAdd(n, .monotonic);
    }
}

comptime {
    if (pool_stats_enabled) {
        @export(&soma_pool_stats_storage, .{ .name = "soma_pool_stats", .linkage = .strong });
    }
}

threadlocal var tls_pools: ?*SomaPools = null;

inline fn getPools() *SomaPools {
    return tls_pools.?;
}

inline fn blockData(block: *SomaPoolBlock) [*]u8 {
    const base: [*]u8 = @ptrCast(block);
    return base + @sizeOf(SomaPoolBlock);
}

fn poolAllocBlock() ?*SomaPoolBlock {
    @branchHint(.cold);
    const total_bytes = @sizeOf(SomaPoolBlock) + POOL_BLOCK_SIZE;
    const raw = somaAlignedAlloc(SOMA_CACHELINE, total_bytes) orelse return null;
    const block: *SomaPoolBlock = @ptrCast(@alignCast(raw));
    block.* = .{ .next = null, .used = 0, ._pad = 0 };
    statInc("blocks_allocated");
    statAdd("bytes_allocated", total_bytes);
    return block;
}

fn poolInit(pool: *SomaPool, item_size: usize) void {
    pool.item_size = item_size;
    pool.free_list = null;
    if (poolAllocBlock()) |block| {
        pool.blocks = block;
        const data = blockData(block);
        pool.bump_ptr = data;
        pool.bump_limit = data + POOL_BLOCK_SIZE;
    } else {
        pool.blocks = null;
        pool.bump_ptr = null;
        pool.bump_limit = null;
    }
}

fn poolCleanup(pool: *SomaPool) void {
    var cur = pool.blocks;
    while (cur) |block| {
        const next = block.next;
        somaAlignedFree(@ptrCast(block));
        cur = next;
    }
    pool.blocks = null;
    pool.free_list = null;
    pool.bump_ptr = null;
    pool.bump_limit = null;
}

inline fn poolAlloc(pool: *SomaPool) ?*anyopaque {
    const item_size = pool.item_size;
    if (pool.bump_ptr) |bp| {
        const new_ptr = bp + item_size;
        if (@intFromPtr(new_ptr) <= @intFromPtr(pool.bump_limit.?)) {
            pool.bump_ptr = new_ptr;
            return @ptrCast(bp);
        }
    }

    if (pool.free_list) |entry| {
        const slot: *?*anyopaque = @ptrCast(@alignCast(entry));
        pool.free_list = slot.*;
        if (pool.free_list) |next| @prefetch(next, .{});
        return entry;
    }

    return poolAllocSlow(pool);
}

fn poolAllocSlow(pool: *SomaPool) ?*anyopaque {
    @branchHint(.cold);
    const new_block = poolAllocBlock() orelse return null;
    new_block.next = pool.blocks;
    pool.blocks = new_block;

    const data = blockData(new_block);
    pool.bump_ptr = data + pool.item_size;
    pool.bump_limit = data + POOL_BLOCK_SIZE;
    return @ptrCast(data);
}

inline fn poolFree(pool: *SomaPool, ptr: *anyopaque) void {
    const slot: *?*anyopaque = @ptrCast(@alignCast(ptr));
    slot.* = pool.free_list;
    pool.free_list = ptr;
}

fn tlsPoolInit() void {
    if (tls_pools != null) return;
    const raw = somaAlignedAlloc(SOMA_CACHELINE, @sizeOf(SomaPools)) orelse return;
    const pools: *SomaPools = @ptrCast(@alignCast(raw));
    poolInit(&pools.pool_48, POOL_SIZE_48);
    poolInit(&pools.pool_112, POOL_SIZE_112);
    tls_pools = pools;
}

fn tlsPoolCleanup() void {
    const pools = tls_pools orelse return;
    poolCleanup(&pools.pool_48);
    poolCleanup(&pools.pool_112);
    somaAlignedFree(@ptrCast(pools));
    tls_pools = null;
}

pub export fn soma_pool_init() void {
    if (comptime pool_stats_enabled) {
        soma_pool_stats_storage = .{};
    }
    tlsPoolInit();
}

pub export fn soma_pool_cleanup() void {
    tlsPoolCleanup();
}

pub export fn soma_pool_alloc_raw(byte_size: usize) ?*anyopaque {
    const pools = getPools();
    if (byte_size <= POOL_SIZE_48) {
        @branchHint(.likely);
        statInc("small_allocs");
        return poolAlloc(&pools.pool_48);
    }
    if (byte_size <= POOL_SIZE_112) {
        statInc("medium_allocs");
        return poolAlloc(&pools.pool_112);
    }
    statInc("large_allocs");
    return malloc(byte_size);
}

pub export fn soma_pool_free_raw(ptr: ?*anyopaque, byte_size: usize) void {
    const pools = getPools();
    const p = ptr orelse return;
    if (byte_size <= POOL_SIZE_48) {
        @branchHint(.likely);
        statInc("small_frees");
        poolFree(&pools.pool_48, p);
    } else if (byte_size <= POOL_SIZE_112) {
        statInc("medium_frees");
        poolFree(&pools.pool_112, p);
    } else {
        statInc("large_frees");
        free(ptr);
    }
}

pub export fn soma_pool_alloc_sup() ?*anyopaque {
    statInc("sup_allocs");
    return poolAlloc(&getPools().pool_48);
}

pub export fn soma_pool_free_sup(ptr: ?*anyopaque) void {
    statInc("sup_frees");
    if (ptr) |p| poolFree(&getPools().pool_48, p);
}

pub export fn soma_alloc_view() ?*anyopaque {
    statInc("small_allocs");
    return poolAlloc(&getPools().pool_48);
}

pub export fn soma_free_view(ptr: ?*anyopaque) void {
    statInc("small_frees");
    if (ptr) |p| poolFree(&getPools().pool_48, p);
}

pub export fn soma_clone_flat_array_view(src: ?*SomaFlatArrayView) ?*anyopaque {
    const v = src orelse return null;

    var new_backing: ?*SomaFlatArray = null;
    var new_data: ?*anyopaque = null;

    if (v.backing) |raw_backing| {
        const src_backing: *SomaFlatArray = @ptrCast(@alignCast(raw_backing));
        const backing_total =
            @sizeOf(SomaFlatArray) +
            @as(usize, @intCast(src_backing.length)) * @as(usize, src_backing.elem_size);
        const new_raw = soma_pool_alloc_raw(backing_total) orelse {
            somaPanic("soma_clone_flat_array_view: out of memory");
        };
        _ = memcpy(new_raw, raw_backing, backing_total);
        const nb: *SomaFlatArray = @ptrCast(@alignCast(new_raw));
        nb._reserved = 0;
        new_backing = nb;

        const src_data_addr = @intFromPtr(v.data orelse unreachable);
        const src_backing_addr = @intFromPtr(raw_backing) + @sizeOf(SomaFlatArray);
        const offset = src_data_addr - src_backing_addr;
        new_data = @ptrFromInt(@intFromPtr(new_raw) + @sizeOf(SomaFlatArray) + offset);
    }

    const dst_raw = soma_alloc_view() orelse {
        somaPanic("soma_clone_flat_array_view: out of memory");
    };
    const dst: *SomaFlatArrayView = @ptrCast(@alignCast(dst_raw));
    dst.tag = NODE_FLAT_ARRAY_VIEW;
    dst._pad = .{ 0, 0, 0 };
    dst._reserved = 0;
    dst.length = v.length;
    dst.data = new_data;
    dst.backing = if (new_backing) |nb| @ptrCast(nb) else null;
    return dst_raw;
}

inline fn listMinCap(elem_size: u16) u32 {
    const per_line = SOMA_CACHELINE / @as(usize, elem_size);
    const clamped: usize = if (per_line < 4) 4 else per_line;
    return @intCast(clamped);
}

pub export fn soma_list_cons(
    elem: ?*const anyopaque,
    tail: SomaList,
    elem_size: u16,
) SomaList {
    var list = tail;

    if (list.offset > 0) {
        @branchHint(.likely);
        list.offset -= 1;
        list.len += 1;
        const base: [*]u8 = @ptrCast(list.data.?);
        const dst = base + @as(usize, list.offset) * @as(usize, elem_size);
        _ = memcpy(dst, elem, elem_size);
        return list;
    }

    const old_len = list.len;
    const min_cap = listMinCap(elem_size);
    var new_cap = old_len *% 2;
    if (new_cap < min_cap) new_cap = min_cap;
    if (new_cap <= old_len) new_cap = old_len + 1;

    const new_bytes = @as(usize, new_cap) * @as(usize, elem_size);
    const new_raw = malloc(new_bytes) orelse {
        somaPanic("soma_list_cons: out of memory");
    };

    var new_offset: u32 = new_cap - old_len;
    if (old_len > 0) {
        const src_base: [*]const u8 = @ptrCast(list.data.?);
        const src = src_base + @as(usize, list.offset) * @as(usize, elem_size);
        const dst_base: [*]u8 = @ptrCast(new_raw);
        const dst = dst_base + @as(usize, new_offset) * @as(usize, elem_size);
        _ = memcpy(dst, src, @as(usize, old_len) * @as(usize, elem_size));
    }
    free(list.data);

    new_offset -= 1;
    const final_dst_base: [*]u8 = @ptrCast(new_raw);
    const final_dst = final_dst_base + @as(usize, new_offset) * @as(usize, elem_size);
    _ = memcpy(final_dst, elem, elem_size);

    return .{ .data = new_raw, .len = old_len + 1, .offset = new_offset };
}

pub export fn soma_list_head(list: SomaList, elem_size: u16) ?*anyopaque {
    const base: [*]u8 = @ptrCast(list.data orelse return null);
    return @ptrCast(base + @as(usize, list.offset) * @as(usize, elem_size));
}

pub export fn soma_list_tail(list: SomaList, elem_size: u16) SomaList {
    _ = elem_size;
    return .{ .data = list.data, .len = list.len - 1, .offset = list.offset + 1 };
}

pub export fn soma_list_dup(list: SomaList, elem_size: u16) SomaList {
    if (list.len == 0) return SOMA_LIST_NIL;
    const live_bytes = @as(usize, list.len) * @as(usize, elem_size);
    const new_raw = malloc(live_bytes) orelse {
        somaPanic("soma_list_dup: out of memory");
    };
    const src_base: [*]const u8 = @ptrCast(list.data.?);
    const src = src_base + @as(usize, list.offset) * @as(usize, elem_size);
    _ = memcpy(new_raw, src, live_bytes);
    return .{ .data = new_raw, .len = list.len, .offset = 0 };
}

pub export fn soma_list_era(list: SomaList) void {
    free(list.data);
}

pub export fn soma_list_from_array(
    data: ?*const anyopaque,
    len: u32,
    elem_size: u16,
) SomaList {
    if (len == 0) return SOMA_LIST_NIL;
    const min_cap = listMinCap(elem_size);
    const cap: u32 = if (len < min_cap) min_cap else len;
    const cap_bytes = @as(usize, cap) * @as(usize, elem_size);
    const buf = malloc(cap_bytes) orelse {
        somaPanic("soma_list_from_array: out of memory");
    };
    const offset: u32 = cap - len;
    const dst_base: [*]u8 = @ptrCast(buf);
    const dst = dst_base + @as(usize, offset) * @as(usize, elem_size);
    _ = memcpy(dst, data, @as(usize, len) * @as(usize, elem_size));
    return .{ .data = buf, .len = len, .offset = offset };
}

fn listBox(list: SomaList, elem_size: u16) *SomaBoxedList {
    const raw = malloc(@sizeOf(SomaBoxedList)) orelse {
        somaPanic("soma_list_box: out of memory");
    };
    const box: *SomaBoxedList = @ptrCast(@alignCast(raw));
    box.* = .{
        .data = list.data,
        .len = list.len,
        .offset = list.offset,
        .elem_size = elem_size,
    };
    return box;
}

pub export fn soma_clone_boxed_list(value: ?*anyopaque, label: u32) ?*anyopaque {
    _ = label;
    const src: *SomaBoxedList = @ptrCast(@alignCast(value orelse return null));
    const dup = soma_list_dup(.{
        .data = src.data,
        .len = src.len,
        .offset = src.offset,
    }, src.elem_size);
    return @ptrCast(listBox(dup, src.elem_size));
}

pub export fn soma_era_boxed_list(value: ?*anyopaque) void {
    const box: *SomaBoxedList = @ptrCast(@alignCast(value orelse return));
    free(box.data);
    free(@ptrCast(box));
}

const soma_boxed_list_typedesc: SomaTypeDesc = .{
    .clone_fn = soma_clone_boxed_list,
    .erase_fn = soma_era_boxed_list,
};

pub export fn soma_list_box_for_sup(list: SomaList, elem_size: u16) ?*anyopaque {
    return @ptrCast(listBox(list, elem_size));
}

pub export fn soma_dup_typed_list(label: u32, boxed_list: ?*anyopaque) SomaValue {
    return soma_dup_typed(label, @intFromPtr(boxed_list), @constCast(&soma_boxed_list_typedesc));
}

pub export fn soma_list_unbox(boxed: ?*anyopaque) SomaList {
    const box: *SomaBoxedList = @ptrCast(@alignCast(boxed orelse return SOMA_LIST_NIL));
    return .{ .data = box.data, .len = box.len, .offset = box.offset };
}

pub export fn soma_clone_heap_value_for_dup(value: ?*anyopaque, label: u32) ?*anyopaque {
    const v = value orelse return null;
    const tag_ptr: *u8 = @ptrCast(v);
    const tag = tag_ptr.*;

    if (isSup(tag)) {
        return @ptrFromInt(soma_dup_typed(label, @intFromPtr(v), null));
    }
    if (tag == NODE_FLAT_ARRAY_VIEW) {
        return soma_clone_flat_array_view(@ptrCast(@alignCast(v)));
    }
    if (tag == NODE_FLAT_ARRAY) {
        const arr: *SomaFlatArray = @ptrCast(@alignCast(v));
        const total =
            @sizeOf(SomaFlatArray) +
            @as(usize, @intCast(arr.length)) * @as(usize, arr.elem_size);
        const copy = malloc(total) orelse {
            somaPanic("soma_clone_heap_value_for_dup: out of memory");
        };
        _ = memcpy(copy, v, total);
        return copy;
    }

    const byte_at_1 = (@as([*]u8, @ptrCast(v)))[1];
    if (byte_at_1 == NODE_CLOSURE) {
        return soma_clone_closure(v, label);
    }

    somaPanic("soma_clone_heap_value_for_dup: unrecognized heap object (missing typed cloner)");
}

pub export fn soma_dup_typed(label: u32, value: SomaValue, type_desc: ?*SomaTypeDesc) SomaValue {
    const raw = soma_pool_alloc_sup() orelse {
        somaPanic("soma_dup_typed: out of memory");
    };
    const sup: *SomaSup = @ptrCast(@alignCast(raw));

    const header_ptr: *align(1) u32 = @ptrCast(&sup.tag);
    header_ptr.* = SOMA_SUP_HEADER_FRESH;

    sup.label = label;
    sup.value = @ptrFromInt(value);
    sup.proj0 = null;
    sup.proj1 = null;
    sup.type_desc = type_desc;
    return @intFromPtr(sup);
}

inline fn isHeapSup(value: SomaValue) bool {
    if (!isPtr(value) or value == 0) return false;
    const sup: *const SomaSup = @ptrCast(@alignCast(toPtr(value).?));
    if (!isSup(sup.tag)) return false;

    const pad_ptr: *align(1) const u32 = @ptrCast(&sup._pad);
    return (pad_ptr.* & 0x00FFFFFF) == SOMA_SUP_MAGIC_U32;
}

fn supCommute(outer: *SomaSup, inner: *SomaSup, proj_idx: u1) SomaValue {
    const w = @intFromPtr(inner.value);
    const inner_label = inner.label;
    const inner_td = inner.type_desc;

    const dup_L_w = soma_dup_typed(outer.label, w, inner_td);
    const w1 = projImpl(dup_L_w, 0);
    const w2 = projImpl(dup_L_w, 1);

    const r0 = soma_dup_typed(inner_label, w1, inner_td);
    const r1 = soma_dup_typed(inner_label, w2, inner_td);

    outer.proj0 = @ptrFromInt(r0);
    outer.proj1 = @ptrFromInt(r1);
    outer.tag = SUP_TAG_BOTH;

    soma_pool_free_sup(@ptrCast(inner));

    return if (proj_idx == 0) r0 else r1;
}

fn projImpl(sup_val: SomaValue, proj_idx: u1) SomaValue {
    if (!isPtr(sup_val) or sup_val == 0) return sup_val;

    const sup: *SomaSup = @ptrCast(@alignCast(toPtr(sup_val).?));
    const tag = sup.tag;

    const my_proj_tag: u8 = if (proj_idx == 0) SUP_TAG_PROJ0 else SUP_TAG_PROJ1;
    const other_proj_tag: u8 = if (proj_idx == 0) SUP_TAG_PROJ1 else SUP_TAG_PROJ0;
    const my_slot: *?*anyopaque = if (proj_idx == 0) &sup.proj0 else &sup.proj1;

    if (tag == SUP_TAG_FRESH) {
        @branchHint(.likely);
        sup.tag = my_proj_tag;
        const value: SomaValue = @intFromPtr(sup.value);

        if (isHeapSup(value)) {
            const inner: *SomaSup = @ptrCast(@alignCast(toPtr(value).?));
            if (inner.label == sup.label) {
                const result: SomaValue = @intFromPtr(inner.value);
                sup.value = @ptrFromInt(result);
                my_slot.* = @ptrFromInt(result);
                soma_pool_free_sup(@ptrCast(inner));
                return result;
            }
            return supCommute(sup, inner, proj_idx);
        }

        my_slot.* = @ptrFromInt(value);
        return value;
    }

    if (tag == other_proj_tag) {
        sup.tag = SUP_TAG_BOTH;
        const value: SomaValue = @intFromPtr(sup.value);

        if (!isPtr(value) or value == 0) {
            my_slot.* = @ptrFromInt(value);
            return value;
        }

        if (isHeapSup(value)) {
            const inner: *SomaSup = @ptrCast(@alignCast(toPtr(value).?));
            if (inner.label == sup.label) {
                const result: SomaValue = @intFromPtr(inner.value);
                sup.value = @ptrFromInt(result);
                my_slot.* = @ptrFromInt(result);
                soma_pool_free_sup(@ptrCast(inner));
                return result;
            }
            return supCommute(sup, inner, proj_idx);
        }

        const cloned: SomaValue = if (sup.type_desc) |td|
            @intFromPtr(td.clone_fn(@ptrFromInt(value), sup.label))
        else
            @intFromPtr(soma_clone_heap_value_for_dup(@ptrFromInt(value), sup.label));
        my_slot.* = @ptrFromInt(cloned);
        return cloned;
    }

    return @intFromPtr(my_slot.*);
}

pub export fn soma_proj0(sup_val: SomaValue) SomaValue {
    return projImpl(sup_val, 0);
}

pub export fn soma_proj1(sup_val: SomaValue) SomaValue {
    return projImpl(sup_val, 1);
}

const SOMA_MAX_CALL_ARGS: comptime_int = 16;

fn CallFnType(comptime n: comptime_int) type {
    var params: [n]std.builtin.Type.Fn.Param = undefined;
    inline for (&params) |*p| p.* = .{
        .is_generic = false,
        .is_noalias = false,
        .type = ?*anyopaque,
    };
    return @Type(.{ .@"fn" = .{
        .calling_convention = .c,
        .is_generic = false,
        .is_var_args = false,
        .return_type = ?*anyopaque,
        .params = &params,
    } });
}

fn somaCallWithArgs(fn_ptr: ?*anyopaque, args: [*]const ?*anyopaque, nargs: u32) ?*anyopaque {
    switch (nargs) {
        inline 0...SOMA_MAX_CALL_ARGS => |n| {
            const FnT = CallFnType(n);
            const fn_typed: *const FnT = @ptrCast(@alignCast(fn_ptr.?));
            var tuple: std.meta.ArgsTuple(FnT) = undefined;
            inline for (0..n) |i| {
                tuple[i] = args[i];
            }
            return @call(.auto, fn_typed, tuple);
        },
        else => {
            @branchHint(.cold);
            somaPanic("soma_call_with_args: too many arguments (max 16)");
        },
    }
}

inline fn closureEnvSize(closure: *const SomaClosure) u16 {
    return @as(u16, closure._pad[1]) | (@as(u16, closure._pad[2]) << 8);
}

inline fn closureEnvBase(closure: *SomaClosure) [*]?*anyopaque {
    const raw: [*]u8 = @ptrCast(closure);
    return @ptrCast(@alignCast(raw + @sizeOf(SomaClosure)));
}

inline fn writeClosureHeader(closure: *SomaClosure, arity: u8, env_size: u16) void {
    const packed_hdr: u32 =
        @as(u32, arity) |
        (@as(u32, NODE_CLOSURE) << 8) |
        (@as(u32, env_size & 0xFF) << 16) |
        (@as(u32, (env_size >> 8) & 0xFF) << 24);
    const hdr_ptr: *align(1) u32 = @ptrCast(&closure.arity);
    hdr_ptr.* = packed_hdr;
}

pub export fn soma_alloc_closure(func_ptr: ?*anyopaque, arity: u8, env_size: u16) ?*anyopaque {
    const byte_size = @sizeOf(SomaClosure) + @as(usize, env_size) * @sizeOf(usize);
    const raw = soma_pool_alloc_raw(byte_size) orelse {
        somaPanic("soma_alloc_closure: out of memory");
    };
    const closure: *SomaClosure = @ptrCast(@alignCast(raw));
    writeClosureHeader(closure, arity, env_size);
    closure.func_ptr = func_ptr;
    return raw;
}

pub export fn soma_closure_set_env(closure_ptr: *anyopaque, index: u16, value: ?*anyopaque) void {
    const closure: *SomaClosure = @ptrCast(@alignCast(closure_ptr));
    const env = closureEnvBase(closure);
    env[index] = value;
}

pub export fn soma_closure_get_env(closure_ptr: *anyopaque, index: u16) ?*anyopaque {
    const closure: *SomaClosure = @ptrCast(@alignCast(closure_ptr));
    const env = closureEnvBase(closure);
    return env[index];
}

pub export fn soma_closure_get_func(closure_ptr: *anyopaque) ?*anyopaque {
    const closure: *SomaClosure = @ptrCast(@alignCast(closure_ptr));
    return closure.func_ptr;
}

pub export fn soma_era_closure(closure_ptr: ?*anyopaque) void {
    const raw = closure_ptr orelse return;
    const closure: *SomaClosure = @ptrCast(@alignCast(raw));
    const env_size = closureEnvSize(closure);
    const env = closureEnvBase(closure);
    var i: u16 = 0;
    while (i < env_size) : (i += 1) {
        const sv: SomaValue = @intFromPtr(env[i]);
        if (isPtr(sv) and sv != 0) {
            soma_era_free(toPtr(sv));
        }
    }

    const byte_size = @sizeOf(SomaClosure) + @as(usize, env_size) * @sizeOf(usize);
    const pools = getPools();
    if (byte_size <= POOL_SIZE_48) {
        @branchHint(.likely);
        statInc("small_frees");
        poolFree(&pools.pool_48, raw);
    } else if (byte_size <= POOL_SIZE_112) {
        statInc("medium_frees");
        poolFree(&pools.pool_112, raw);
    } else {
        statInc("large_frees");
        free(raw);
    }
}

pub export fn soma_apply(closure_ptr: ?*anyopaque, arg: ?*anyopaque) ?*anyopaque {
    var closure: *SomaClosure = @ptrCast(@alignCast(closure_ptr orelse return null));
    var arity = closure.arity;
    var fn_ptr = closure.func_ptr;
    var env = closureEnvBase(closure);
    var env_size = closureEnvSize(closure);

    while (arity == 0) {
        @branchHint(.unlikely);
        var stage: [SOMA_MAX_CALL_ARGS]?*anyopaque = undefined;
        const n = @min(env_size, @as(u16, SOMA_MAX_CALL_ARGS));
        var i: u16 = 0;
        while (i < n) : (i += 1) stage[i] = env[i];
        const result = somaCallWithArgs(fn_ptr, &stage, n);
        closure = @ptrCast(@alignCast(result orelse return null));
        arity = closure.arity;
        fn_ptr = closure.func_ptr;
        env = closureEnvBase(closure);
        env_size = closureEnvSize(closure);
    }

    if (arity == 1) {
        @branchHint(.likely);
        var stage: [SOMA_MAX_CALL_ARGS]?*anyopaque = undefined;
        const n: u16 = @min(env_size, @as(u16, SOMA_MAX_CALL_ARGS - 1));
        var i: u16 = 0;
        while (i < n) : (i += 1) stage[i] = env[i];
        stage[n] = arg;
        return somaCallWithArgs(fn_ptr, &stage, @as(u32, n) + 1);
    }

    const new_env_size: u16 = env_size + 1;
    const pap_bytes = @sizeOf(SomaClosure) + @as(usize, new_env_size) * @sizeOf(usize);
    const pap_raw = soma_pool_alloc_raw(pap_bytes) orelse {
        somaPanic("soma_apply: out of memory for PAP");
    };
    const pap: *SomaClosure = @ptrCast(@alignCast(pap_raw));
    writeClosureHeader(pap, arity - 1, new_env_size);
    pap.func_ptr = closure.func_ptr;

    const pap_env = closureEnvBase(pap);
    if (env_size > 0) {
        _ = memcpy(@ptrCast(pap_env), @ptrCast(env), @as(usize, env_size) * @sizeOf(usize));
    }
    pap_env[env_size] = arg;
    return pap_raw;
}

pub export fn soma_clone_closure(closure_ptr: ?*anyopaque, label: u32) ?*anyopaque {
    const raw = closure_ptr orelse return null;
    const closure: *SomaClosure = @ptrCast(@alignCast(raw));
    const env_size = closureEnvSize(closure);

    const byte_size = @sizeOf(SomaClosure) + @as(usize, env_size) * @sizeOf(usize);
    const new_raw = soma_pool_alloc_raw(byte_size) orelse {
        somaPanic("soma_clone_closure: out of memory");
    };

    if (env_size == 0) {
        _ = memcpy(new_raw, raw, @sizeOf(SomaClosure));
        return new_raw;
    }

    const src_env = closureEnvBase(closure);
    var has_heap = false;
    var i: u16 = 0;
    while (i < env_size) : (i += 1) {
        const sv: SomaValue = @intFromPtr(src_env[i]);
        if (isPtr(sv) and sv != 0) {
            has_heap = true;
            break;
        }
    }

    if (!has_heap) {
        _ = memcpy(new_raw, raw, byte_size);
        return new_raw;
    }

    _ = memcpy(new_raw, raw, @sizeOf(SomaClosure));
    const new_closure: *SomaClosure = @ptrCast(@alignCast(new_raw));
    const dst_env = closureEnvBase(new_closure);
    i = 0;
    while (i < env_size) : (i += 1) {
        dst_env[i] = soma_clone_heap_value_for_dup(src_env[i], label);
    }
    return new_raw;
}

pub export fn soma_from_cstring(cstr: ?[*:0]const u8) SomaString {
    const s = cstr orelse return .{ .data = null, .len = 0 };
    const len = strlen(s);
    const buf_raw = soma_pool_alloc_raw(len + 1) orelse {
        somaPanic("soma_from_cstring: out of memory");
    };
    _ = memcpy(buf_raw, @as(*const anyopaque, @ptrCast(s)), len + 1);
    return .{ .data = @ptrCast(buf_raw), .len = @intCast(len) };
}

pub export fn soma_strcat(a: SomaString, b: SomaString) SomaString {
    const len_a: usize = @intCast(somaStringLen(a));
    const len_b: usize = @intCast(somaStringLen(b));
    const total_len = len_a + len_b;
    const buf_raw = soma_pool_alloc_raw(total_len + 1) orelse {
        somaPanic("soma_strcat: out of memory");
    };
    const buf: [*]u8 = @ptrCast(buf_raw);
    if (len_a != 0) _ = memcpy(buf_raw, @ptrCast(a.data), len_a);
    if (len_b != 0) _ = memcpy(@ptrCast(buf + len_a), @ptrCast(b.data), len_b);
    buf[total_len] = 0;
    return .{ .data = buf, .len = @intCast(total_len) };
}

pub export fn soma_int_to_string(val: i32) SomaString {
    var tmp: [12]u8 = undefined;
    var end: usize = tmp.len;
    end -= 1;
    tmp[end] = 0;

    const negative = val < 0;

    var uval: u32 = if (negative)
        @intCast(-@as(i64, val))
    else
        @intCast(val);

    if (uval == 0) {
        end -= 1;
        tmp[end] = '0';
    } else {
        while (uval > 0) {
            end -= 1;
            tmp[end] = '0' + @as(u8, @intCast(uval % 10));
            uval /= 10;
        }
    }
    if (negative) {
        end -= 1;
        tmp[end] = '-';
    }

    const len = tmp.len - 1 - end;
    const buf_raw = soma_pool_alloc_raw(len + 1) orelse {
        somaPanic("soma_int_to_string: out of memory");
    };
    _ = memcpy(buf_raw, @ptrCast(&tmp[end]), len + 1);
    return .{ .data = @ptrCast(buf_raw), .len = @intCast(len) };
}

pub export fn soma_era_string(str: SomaString) void {
    const data = str.data orelse return;
    if (str.len < 0) return;
    soma_pool_free_raw(@ptrCast(data), @as(usize, @intCast(str.len)) + 1);
}

const ERA_STACK_INLINE: comptime_int = 64;

pub export fn soma_era_free(value: ?*anyopaque) void {
    const root = value orelse return;

    var stack_buf: [ERA_STACK_INLINE]?*anyopaque = undefined;
    var stack: []?*anyopaque = stack_buf[0..];
    var sp: usize = 0;
    var cap: usize = ERA_STACK_INLINE;
    var heap_backed = false;
    defer if (heap_backed) free(@ptrCast(stack.ptr));

    const ensure = struct {
        fn call(
            sp_in: usize,
            n: usize,
            stk_ptr: *[]?*anyopaque,
            cap_ptr: *usize,
            heap_ptr: *bool,
            buf_ptr: *[ERA_STACK_INLINE]?*anyopaque,
        ) void {
            if (sp_in + n <= cap_ptr.*) return;
            var new_cap = cap_ptr.* * 2;
            while (new_cap < sp_in + n) : (new_cap *= 2) {}
            if (!heap_ptr.*) {
                const raw = malloc(new_cap * @sizeOf(?*anyopaque)) orelse
                    somaPanic("soma_era_free: out of memory");
                const new_slice = @as([*]?*anyopaque, @ptrCast(@alignCast(raw)))[0..new_cap];
                @memcpy(new_slice[0..sp_in], buf_ptr[0..sp_in]);
                stk_ptr.* = new_slice;
                heap_ptr.* = true;
            } else {
                const raw = realloc(@ptrCast(stk_ptr.ptr), new_cap * @sizeOf(?*anyopaque)) orelse
                    somaPanic("soma_era_free: out of memory");
                stk_ptr.* = @as([*]?*anyopaque, @ptrCast(@alignCast(raw)))[0..new_cap];
            }
            cap_ptr.* = new_cap;
        }
    }.call;

    stack[sp] = root;
    sp += 1;

    const pools = getPools();

    while (sp > 0) {
        sp -= 1;
        const cur = stack[sp] orelse continue;
        const tag_ptr: *u8 = @ptrCast(cur);
        const tag = tag_ptr.*;

        if (tag == NODE_FLAT_ARRAY_VIEW) {
            const view: *SomaFlatArrayView = @ptrCast(@alignCast(cur));
            if (view.backing) |backing_raw| {
                const backing: *SomaFlatArray = @ptrCast(@alignCast(backing_raw));
                const backing_size =
                    @sizeOf(SomaFlatArray) +
                    @as(usize, @intCast(backing.length)) * @as(usize, backing.elem_size);
                soma_pool_free_raw(backing_raw, backing_size);
            }
            statInc("small_frees");
            poolFree(&pools.pool_48, cur);
        } else if (tag == NODE_FLAT_ARRAY) {
            free(cur);
        } else if (isSup(tag)) {
            const sup: *SomaSup = @ptrCast(@alignCast(cur));
            const v: SomaValue = @intFromPtr(sup.value);
            const efn_opt: ?SomaEraseFn = if (sup.type_desc) |td| td.erase_fn else null;

            switch (sup.tag) {
                SUP_TAG_FRESH, SUP_TAG_PROJ0, SUP_TAG_PROJ1 => {
                    if (isPtr(v) and v != 0) {
                        if (efn_opt) |efn| {
                            efn(@ptrFromInt(v));
                        } else {
                            ensure(sp, 1, &stack, &cap, &heap_backed, &stack_buf);
                            stack[sp] = toPtr(v);
                            sp += 1;
                        }
                    }
                },
                else => {
                    const p0: SomaValue = @intFromPtr(sup.proj0);
                    const p1: SomaValue = @intFromPtr(sup.proj1);
                    if (efn_opt) |efn| {
                        if (isPtr(v) and v != 0) efn(@ptrFromInt(v));
                        if (p0 != v and isPtr(p0) and p0 != 0) efn(@ptrFromInt(p0));
                        if (p1 != v and p1 != p0 and isPtr(p1) and p1 != 0) efn(@ptrFromInt(p1));
                    } else {
                        ensure(sp, 3, &stack, &cap, &heap_backed, &stack_buf);
                        if (isPtr(v) and v != 0) {
                            stack[sp] = toPtr(v);
                            sp += 1;
                        }
                        if (p0 != v and isPtr(p0) and p0 != 0) {
                            stack[sp] = toPtr(p0);
                            sp += 1;
                        }
                        if (p1 != v and p1 != p0 and isPtr(p1) and p1 != 0) {
                            stack[sp] = toPtr(p1);
                            sp += 1;
                        }
                    }
                },
            }

            statInc("sup_frees");
            poolFree(&pools.pool_48, cur);
        } else {
            const byte_at_1 = (@as([*]u8, @ptrCast(cur)))[1];
            if (byte_at_1 == NODE_CLOSURE) {
                const closure: *SomaClosure = @ptrCast(@alignCast(cur));
                const es = closureEnvSize(closure);
                const env = closureEnvBase(closure);
                ensure(sp, es, &stack, &cap, &heap_backed, &stack_buf);
                var i: u16 = 0;
                while (i < es) : (i += 1) {
                    const sv: SomaValue = @intFromPtr(env[i]);
                    if (isPtr(sv) and sv != 0) {
                        stack[sp] = toPtr(sv);
                        sp += 1;
                    }
                }
                const needed = @sizeOf(SomaClosure) + @as(usize, es) * @sizeOf(usize);
                if (needed <= POOL_SIZE_48) {
                    @branchHint(.likely);
                    statInc("small_frees");
                    poolFree(&pools.pool_48, cur);
                } else if (needed <= POOL_SIZE_112) {
                    statInc("medium_frees");
                    poolFree(&pools.pool_112, cur);
                } else {
                    statInc("large_frees");
                    free(cur);
                }
            } else {
                somaPanic("soma_era_free: unrecognized heap object (missing typed eraser)");
            }
        }
    }
}

fn somaPanic(comptime msg: []const u8) noreturn {
    @branchHint(.cold);
    writeStderr("PANIC: " ++ msg ++ "\n");
    tlsPoolCleanup();
    exit(1);
}

pub export fn soma_panic(msg: ?[*:0]const u8) noreturn {
    @branchHint(.cold);
    writeStderr("PANIC: ");
    if (msg) |m| {
        writeStderr(std.mem.sliceTo(m, 0));
    } else {
        writeStderr("(null)");
    }
    writeStderr("\n");
    tlsPoolCleanup();
    exit(1);
}

extern "c" fn soma_main() c_int;

comptime {
    if (!opts.no_main) {
        @export(&somaMain, .{ .name = "main", .linkage = .strong });
    }
}

fn somaMain() callconv(.c) c_int {
    soma_pool_init();
    const result = soma_main();
    soma_pool_cleanup();
    return result;
}
