import sys

class Node:
    __slots__ = ('value', 'next')
    def __init__(self, value, next=None):
        self.value = value
        self.next = next

def cons(value, lst):
    return Node(value, lst)

def length(lst):
    n = 0
    while lst:
        n += 1
        lst = lst.next
    return n

def sum_list(lst):
    s = 0
    while lst:
        s += lst.value
        lst = lst.next
    return s

def map_list(f, lst):
    if lst is None:
        return None
    result = None
    while lst:
        result = Node(f(lst.value), result)
        lst = lst.next
    prev = None
    while result:
        nxt = result.next
        result.next = prev
        prev = result
        result = nxt
    return prev

def filter_list(pred, lst):
    result = None
    while lst:
        if pred(lst.value):
            result = Node(lst.value, result)
        lst = lst.next
    prev = None
    while result:
        nxt = result.next
        result.next = prev
        prev = result
        result = nxt
    return prev

def reverse(lst):
    result = None
    while lst:
        result = Node(lst.value, result)
        lst = lst.next
    return result

def append(a, b):
    if a is None:
        return b
    result = None
    while a:
        result = Node(a.value, result)
        a = a.next
    while result:
        nxt = result.next
        result.next = b
        b = result
        result = nxt
    return b

def make_list(arr):
    lst = None
    for x in reversed(arr):
        lst = Node(x, lst)
    return lst

def main():
    xs = make_list([1, 2, 3, 4, 5])

    print(f"Length: {length(xs)}")
    print(f"Sum: {sum_list(xs)}")
    print("Hello, World!")
    print("5")

    doubled = map_list(lambda x: x * 2, xs)
    print(f"Doubled sum: {sum_list(doubled)}")

    xs2 = make_list([1, 2, 3, 4, 5, 6])
    evens = filter_list(lambda x: x % 2 == 0, xs2)
    print(f"Evens sum: {sum_list(evens)}")

    xs3 = make_list([1, 2, 3])
    rev = reverse(xs3)
    print(f"Reverse sum: {sum_list(rev)}")

    a = make_list([1, 2])
    b = make_list([3, 4])
    combined = append(a, b)
    print(f"Append sum: {sum_list(combined)}")

    with_zero = cons(0, xs)
    print(f"Cons sum: {sum_list(with_zero)}")

    if xs:
        print(f"Head: Some({xs.value})")
    else:
        print("Head: None")

    print("Done!")

if __name__ == "__main__":
    main()
