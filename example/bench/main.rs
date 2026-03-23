fn main() {
    let xs: Vec<i32> = vec![1, 2, 3, 4, 5];

    println!("Length: {}", xs.len());
    println!("Sum: {}", xs.iter().sum::<i32>());
    println!("Hello, World!");
    println!("5");

    let doubled: Vec<i32> = xs.iter().map(|x| x * 2).collect();
    println!("Doubled sum: {}", doubled.iter().sum::<i32>());

    let evens: Vec<i32> = vec![1, 2, 3, 4, 5, 6].into_iter().filter(|x| x % 2 == 0).collect();
    println!("Evens sum: {}", evens.iter().sum::<i32>());

    let rev: Vec<i32> = vec![1, 2, 3].into_iter().rev().collect();
    println!("Reverse sum: {}", rev.iter().sum::<i32>());

    let mut combined = vec![1, 2];
    combined.extend(&[3, 4]);
    println!("Append sum: {}", combined.iter().sum::<i32>());

    let mut with_zero = vec![0];
    with_zero.extend(&xs);
    println!("Cons sum: {}", with_zero.iter().sum::<i32>());

    match xs.first() {
        Some(v) => println!("Head: Some({})", v),
        None => println!("Head: None"),
    }

    // Cross-producer fusion: map over filter
    let mf_sum: i32 = vec![1, 2, 3, 4, 5, 6]
        .into_iter()
        .filter(|x| x % 2 == 0)
        .map(|x| x * 10)
        .sum();
    println!("Map-filter sum: {}", mf_sum);

    // Cross-producer fusion: filter over map
    let fm_sum: i32 = vec![1, 2, 3, 4, 5]
        .into_iter()
        .map(|x| x * 2)
        .filter(|x| x % 3 == 0)
        .sum();
    println!("Filter-map sum: {}", fm_sum);

    println!("Done!");
}
