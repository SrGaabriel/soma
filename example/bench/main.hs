main :: IO ()
main = do
    let xs = [1, 2, 3, 4, 5] :: [Int]

    putStrLn $ "Length: " ++ show (length xs)
    putStrLn $ "Sum: " ++ show (sum xs)
    putStrLn "Hello, World!"
    putStrLn "5"

    let doubled = map (* 2) xs
    putStrLn $ "Doubled sum: " ++ show (sum doubled)

    let evens = filter even [1, 2, 3, 4, 5, 6 :: Int]
    putStrLn $ "Evens sum: " ++ show (sum evens)

    let rev = reverse [1, 2, 3 :: Int]
    putStrLn $ "Reverse sum: " ++ show (sum rev)

    let combined = [1, 2] ++ [3, 4 :: Int]
    putStrLn $ "Append sum: " ++ show (sum combined)

    let withZero = 0 : xs
    putStrLn $ "Cons sum: " ++ show (sum withZero)

    case xs of
        (h:_) -> putStrLn $ "Head: Some(" ++ show h ++ ")"
        []    -> putStrLn "Head: None"

    -- Cross-producer fusion: map over filter
    let mfSum = sum $ map (* 10) $ filter even [1, 2, 3, 4, 5, 6 :: Int]
    putStrLn $ "Map-filter sum: " ++ show mfSum

    -- Cross-producer fusion: filter over map
    let fmSum = sum $ filter (\x -> x `mod` 3 == 0) $ map (* 2) [1, 2, 3, 4, 5 :: Int]
    putStrLn $ "Filter-map sum: " ++ show fmSum

    putStrLn "Done!"
