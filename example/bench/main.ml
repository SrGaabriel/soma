let sum = List.fold_left (+) 0

let () =
  let xs = [1; 2; 3; 4; 5] in

  Printf.printf "Length: %d\n" (List.length xs);
  Printf.printf "Sum: %d\n" (sum xs);
  print_endline "Hello, World!";
  print_endline "5";

  let doubled = List.map (fun x -> x * 2) xs in
  Printf.printf "Doubled sum: %d\n" (sum doubled);

  let evens = List.filter (fun x -> x mod 2 = 0) [1; 2; 3; 4; 5; 6] in
  Printf.printf "Evens sum: %d\n" (sum evens);

  let rev = List.rev [1; 2; 3] in
  Printf.printf "Reverse sum: %d\n" (sum rev);

  let combined = [1; 2] @ [3; 4] in
  Printf.printf "Append sum: %d\n" (sum combined);

  let with_zero = 0 :: xs in
  Printf.printf "Cons sum: %d\n" (sum with_zero);

  (match xs with
   | h :: _ -> Printf.printf "Head: Some(%d)\n" h
   | [] -> print_endline "Head: None");

  (* Cross-producer fusion: map over filter *)
  let mf = List.map (fun x -> x * 10) (List.filter (fun x -> x mod 2 = 0) [1; 2; 3; 4; 5; 6]) in
  Printf.printf "Map-filter sum: %d\n" (sum mf);

  (* Cross-producer fusion: filter over map *)
  let fm = List.filter (fun x -> x mod 3 = 0) (List.map (fun x -> x * 2) [1; 2; 3; 4; 5]) in
  Printf.printf "Filter-map sum: %d\n" (sum fm);

  print_endline "Done!"
