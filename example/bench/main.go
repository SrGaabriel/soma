package main

import "fmt"

func sum(xs []int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

func mapList(f func(int) int, xs []int) []int {
	result := make([]int, len(xs))
	for i, x := range xs {
		result[i] = f(x)
	}
	return result
}

func filterList(pred func(int) bool, xs []int) []int {
	var result []int
	for _, x := range xs {
		if pred(x) {
			result = append(result, x)
		}
	}
	return result
}

func main() {
	xs := []int{1, 2, 3, 4, 5}

	fmt.Printf("Length: %d\n", len(xs))
	fmt.Printf("Sum: %d\n", sum(xs))
	fmt.Println("Hello, World!")
	fmt.Println("5")

	doubled := mapList(func(x int) int { return x * 2 }, xs)
	fmt.Printf("Doubled sum: %d\n", sum(doubled))

	evens := filterList(func(x int) bool { return x%2 == 0 }, []int{1, 2, 3, 4, 5, 6})
	fmt.Printf("Evens sum: %d\n", sum(evens))

	rev := make([]int, 3)
	for i, v := range []int{1, 2, 3} {
		rev[2-i] = v
	}
	fmt.Printf("Reverse sum: %d\n", sum(rev))

	combined := append([]int{1, 2}, []int{3, 4}...)
	fmt.Printf("Append sum: %d\n", sum(combined))

	withZero := append([]int{0}, xs...)
	fmt.Printf("Cons sum: %d\n", sum(withZero))

	if len(xs) > 0 {
		fmt.Printf("Head: Some(%d)\n", xs[0])
	} else {
		fmt.Println("Head: None")
	}

	fmt.Println("Done!")
}
