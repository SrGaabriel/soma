class Node {
    constructor(value, next) {
        this.value = value;
        this.next = next || null;
    }
}

function cons(value, list) {
    return new Node(value, list);
}

function length(list) {
    let n = 0;
    while (list) { n++; list = list.next; }
    return n;
}

function sum(list) {
    let s = 0;
    while (list) { s += list.value; list = list.next; }
    return s;
}

function map(f, list) {
    if (!list) return null;
    let result = null;
    for (let n = list; n; n = n.next)
        result = new Node(f(n.value), result);
    let prev = null;
    while (result) {
        const next = result.next;
        result.next = prev;
        prev = result;
        result = next;
    }
    return prev;
}

function filter(pred, list) {
    let result = null;
    for (let n = list; n; n = n.next)
        if (pred(n.value))
            result = new Node(n.value, result);
    let prev = null;
    while (result) {
        const next = result.next;
        result.next = prev;
        prev = result;
        result = next;
    }
    return prev;
}

function reverse(list) {
    let result = null;
    for (let n = list; n; n = n.next)
        result = new Node(n.value, result);
    return result;
}

function append(a, b) {
    if (!a) return b;
    let result = null;
    for (let n = a; n; n = n.next)
        result = new Node(n.value, result);
    while (result) {
        const next = result.next;
        result.next = b;
        b = result;
        result = next;
    }
    return b;
}

function makeList(arr) {
    let list = null;
    for (let i = arr.length - 1; i >= 0; i--)
        list = new Node(arr[i], list);
    return list;
}

const xs = makeList([1, 2, 3, 4, 5]);

console.log(`Length: ${length(xs)}`);
console.log(`Sum: ${sum(xs)}`);
console.log("Hello, World!");
console.log("5");

const doubled = map(x => x * 2, xs);
console.log(`Doubled sum: ${sum(doubled)}`);

const xs2 = makeList([1, 2, 3, 4, 5, 6]);
const evens = filter(x => x % 2 === 0, xs2);
console.log(`Evens sum: ${sum(evens)}`);

const xs3 = makeList([1, 2, 3]);
const rev = reverse(xs3);
console.log(`Reverse sum: ${sum(rev)}`);

const a = makeList([1, 2]);
const b = makeList([3, 4]);
const combined = append(a, b);
console.log(`Append sum: ${sum(combined)}`);

const withZero = cons(0, xs);
console.log(`Cons sum: ${sum(withZero)}`);

if (xs) console.log(`Head: Some(${xs.value})`);
else console.log("Head: None");

// Cross-producer fusion: map over filter
const mf = map(x => x * 10, filter(x => x % 2 === 0, makeList([1, 2, 3, 4, 5, 6])));
console.log(`Map-filter sum: ${sum(mf)}`);

// Cross-producer fusion: filter over map
const fm = filter(x => x % 3 === 0, map(x => x * 2, makeList([1, 2, 3, 4, 5])));
console.log(`Filter-map sum: ${sum(fm)}`);

console.log("Done!");
