module Lib
    ( someFunc
    ) where

helper :: Int -> String

helper n
    | n `mod` 15 == 0 = "FizzBuzz"
    | n `mod` 5 == 0 = "Buzz"
    | n `mod` 3 == 0 = "Fizz"
    | otherwise = show n

someFunc :: IO ()
someFunc = map (putStrLn helper) [1..100]
