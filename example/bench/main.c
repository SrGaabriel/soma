#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Simple linked list for fair comparison */
typedef struct Node {
    int value;
    struct Node* next;
} Node;

static Node* cons(int value, Node* next) {
    Node* n = malloc(sizeof(Node));
    n->value = value;
    n->next = next;
    return n;
}

static void free_list(Node* list) {
    while (list) {
        Node* next = list->next;
        free(list);
        list = next;
    }
}

static int length(Node* list) {
    int len = 0;
    for (Node* n = list; n; n = n->next) len++;
    return len;
}

static int sum(Node* list) {
    int s = 0;
    for (Node* n = list; n; n = n->next) s += n->value;
    return s;
}

static Node* map(int (*f)(int), Node* list) {
    if (!list) return NULL;
    /* Build in reverse, then reverse */
    Node* result = NULL;
    for (Node* n = list; n; n = n->next)
        result = cons(f(n->value), result);
    /* Reverse */
    Node* prev = NULL;
    while (result) {
        Node* next = result->next;
        result->next = prev;
        prev = result;
        result = next;
    }
    return prev;
}

static Node* filter(int (*pred)(int), Node* list) {
    Node* result = NULL;
    for (Node* n = list; n; n = n->next)
        if (pred(n->value))
            result = cons(n->value, result);
    Node* prev = NULL;
    while (result) {
        Node* next = result->next;
        result->next = prev;
        prev = result;
        result = next;
    }
    return prev;
}

static Node* reverse(Node* list) {
    Node* result = NULL;
    for (Node* n = list; n; n = n->next)
        result = cons(n->value, result);
    return result;
}

static Node* append(Node* a, Node* b) {
    if (!a) return b;
    Node* result = NULL;
    for (Node* n = a; n; n = n->next)
        result = cons(n->value, result);
    /* Reverse onto b */
    while (result) {
        Node* next = result->next;
        result->next = b;
        b = result;
        result = next;
    }
    return b;
}

static int double_val(int x) { return x * 2; }
static int is_even(int x) { return x % 2 == 0; }

static Node* make_list(int* arr, int n) {
    Node* list = NULL;
    for (int i = n - 1; i >= 0; i--)
        list = cons(arr[i], list);
    return list;
}

int main(void) {
    int arr[] = {1, 2, 3, 4, 5};
    Node* xs = make_list(arr, 5);

    printf("Length: %d\n", length(xs));
    printf("Sum: %d\n", sum(xs));
    printf("Hello, World!\n");
    printf("5\n");

    Node* doubled = map(double_val, xs);
    printf("Doubled sum: %d\n", sum(doubled));
    free_list(doubled);

    int arr2[] = {1, 2, 3, 4, 5, 6};
    Node* xs2 = make_list(arr2, 6);
    Node* evens = filter(is_even, xs2);
    printf("Evens sum: %d\n", sum(evens));
    free_list(evens);
    free_list(xs2);

    int arr3[] = {1, 2, 3};
    Node* xs3 = make_list(arr3, 3);
    Node* rev = reverse(xs3);
    printf("Reverse sum: %d\n", sum(rev));
    free_list(rev);
    free_list(xs3);

    int arr4[] = {1, 2};
    int arr5[] = {3, 4};
    Node* a = make_list(arr4, 2);
    Node* b = make_list(arr5, 2);
    Node* combined = append(a, b);
    printf("Append sum: %d\n", sum(combined));
    free_list(combined);
    free_list(a);

    Node* withZero = cons(0, xs);
    printf("Cons sum: %d\n", sum(withZero));

    if (xs) printf("Head: Some(%d)\n", xs->value);
    else printf("Head: None\n");

    printf("Done!\n");

    free_list(withZero);
    return 0;
}
