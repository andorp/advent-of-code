module Day1

import Data.SortedSet
import System.File
import Data.Strings


testList : List Int
testList =
  [ 1721
  , 979
  , 366
  , 299
  , 675
  , 1456
  , 1701
  ]

parseContent : String -> List Int
parseContent s = map cast $ lines s

-- Brute force
brutePair : List Int -> List Int
brutePair xs =
  [ (x * y)
  | x <- xs
  , y <- xs
  , x /= y
  , x + y == 2020
  ]

-- Something smarter
findPair : Int -> List Int -> Maybe Int
findPair s = go empty
  where
    go : SortedSet Int -> List Int -> Maybe Int
    go found [] = Nothing
    go found (x :: xs) = case contains x found of
          False => go (insert (s - x) found) xs
          True  => Just ((s - x) * x)

-- Brute force
bruteTriplet : List Int -> List Int
bruteTriplet xs =
  [ (x * y * z)
  | x <- xs
  , y <- xs
  , z <- xs
  , x /= y || y /= z || z /= x
  , x + y + z == 2020
  ]

-- Something smarter
findTriplet : List Int -> Maybe Int
findTriplet [] = Nothing
findTriplet (x :: xs) = case findPair (2020 - x) xs of
  Nothing => findTriplet xs
  Just s => Just (x * s)

main : IO ()
main = do
  Right content <- readFile "day1i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  let expenses = parseContent content
  -- let expenses = testList
  putStrLn "First part"
  printLn $ findPair 2020 expenses
  putStrLn "Second part"
  printLn $ findTriplet expenses
