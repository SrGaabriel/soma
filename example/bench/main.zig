const std = @import("std");
const c = @cImport({
    @cInclude("stdio.h");
    @cInclude("stdlib.h");
});

const Node = struct {
    value: c_int,
    next: ?*Node,
};

fn cons(value: c_int, next: ?*Node) *Node {
    const raw = c.malloc(@sizeOf(Node)) orelse @panic("OOM");
    const n: *Node = @ptrCast(@alignCast(raw));
    n.* = .{ .value = value, .next = next };
    return n;
}

fn freeList(list_: ?*Node) void {
    var list = list_;
    while (list) |n| {
        const next = n.next;
        c.free(@ptrCast(n));
        list = next;
    }
}

fn length(list_: ?*Node) c_int {
    var list = list_;
    var len: c_int = 0;
    while (list) |n| {
        len += 1;
        list = n.next;
    }
    return len;
}

fn sum(list_: ?*Node) c_int {
    var list = list_;
    var s: c_int = 0;
    while (list) |n| {
        s += n.value;
        list = n.next;
    }
    return s;
}

fn map(f: *const fn (c_int) callconv(.c) c_int, list_: ?*Node) ?*Node {
    var list = list_;
    if (list == null) return null;
    var result: ?*Node = null;
    while (list) |n| {
        result = cons(f(n.value), result);
        list = n.next;
    }
    var prev: ?*Node = null;
    while (result) |r| {
        const next = r.next;
        r.next = prev;
        prev = r;
        result = next;
    }
    return prev;
}

fn filter(pred: *const fn (c_int) callconv(.c) c_int, list_: ?*Node) ?*Node {
    var list = list_;
    var result: ?*Node = null;
    while (list) |n| {
        if (pred(n.value) != 0) {
            result = cons(n.value, result);
        }
        list = n.next;
    }
    var prev: ?*Node = null;
    while (result) |r| {
        const next = r.next;
        r.next = prev;
        prev = r;
        result = next;
    }
    return prev;
}

fn reverse(list_: ?*Node) ?*Node {
    var list = list_;
    var result: ?*Node = null;
    while (list) |n| {
        result = cons(n.value, result);
        list = n.next;
    }
    return result;
}

fn append(a_: ?*Node, b_: ?*Node) ?*Node {
    var a = a_;
    var b = b_;
    if (a == null) return b;
    var result: ?*Node = null;
    while (a) |n| {
        result = cons(n.value, result);
        a = n.next;
    }
    while (result) |r| {
        const next = r.next;
        r.next = b;
        b = r;
        result = next;
    }
    return b;
}

fn makeList(arr: []const c_int) ?*Node {
    var list: ?*Node = null;
    var i: usize = arr.len;
    while (i > 0) {
        i -= 1;
        list = cons(arr[i], list);
    }
    return list;
}

fn doubleVal(x: c_int) callconv(.c) c_int {
    return x * 2;
}

fn isEven(x: c_int) callconv(.c) c_int {
    return if (@mod(x, 2) == 0) @as(c_int, 1) else @as(c_int, 0);
}

pub fn main() void {
    const xs = makeList(&[_]c_int{ 1, 2, 3, 4, 5 });

    _ = c.printf("Length: %d\n", length(xs));
    _ = c.printf("Sum: %d\n", sum(xs));
    _ = c.printf("Hello, World!\n");
    _ = c.printf("5\n");

    const doubled = map(&doubleVal, xs);
    _ = c.printf("Doubled sum: %d\n", sum(doubled));
    freeList(doubled);

    const xs2 = makeList(&[_]c_int{ 1, 2, 3, 4, 5, 6 });
    const evens = filter(&isEven, xs2);
    _ = c.printf("Evens sum: %d\n", sum(evens));
    freeList(evens);
    freeList(xs2);

    const xs3 = makeList(&[_]c_int{ 1, 2, 3 });
    const rev = reverse(xs3);
    _ = c.printf("Reverse sum: %d\n", sum(rev));
    freeList(rev);
    freeList(xs3);

    const a = makeList(&[_]c_int{ 1, 2 });
    const b = makeList(&[_]c_int{ 3, 4 });
    const combined = append(a, b);
    _ = c.printf("Append sum: %d\n", sum(combined));
    freeList(combined);
    freeList(a);

    const withZero = cons(0, xs.?);
    _ = c.printf("Cons sum: %d\n", sum(withZero));

    if (xs) |head| {
        _ = c.printf("Head: Some(%d)\n", head.value);
    } else {
        _ = c.printf("Head: None\n");
    }

    _ = c.printf("Done!\n");

    freeList(withZero);
}
