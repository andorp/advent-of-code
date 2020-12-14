module Day1

{-
--- Day 1: Report Repair ---
After saving Christmas five years in a row, you've decided to take a vacation at a nice resort on a tropical island. Surely, Christmas will go on without you.

The tropical island has its own currency and is entirely cash-only. The gold coins used there have a little picture of a starfish; the locals just call them stars. None of the currency exchanges seem to have heard of them, but somehow, you'll need to find fifty of these coins by the time you arrive so you can pay the deposit on your room.

To save your vacation, you need to get all fifty stars by December 25th.

Collect stars by solving puzzles. Two puzzles will be made available on each day in the Advent calendar; the second puzzle is unlocked when you complete the first. Each puzzle grants one star. Good luck!

Before you leave, the Elves in accounting just need you to fix your expense report (your puzzle input); apparently, something isn't quite adding up.

Specifically, they need you to find the two entries that sum to 2020 and then multiply those two numbers together.

For example, suppose your expense report contained the following:

1721
979
366
299
675
1456
In this list, the two entries that sum to 2020 are 1721 and 299. Multiplying them together produces 1721 * 299 = 514579, so the correct answer is 514579.

Of course, your expense report is much larger. Find the two entries that sum to 2020; what do you get if you multiply them together?

Your puzzle answer was 1016964.

--- Part Two ---
The Elves in accounting are thankful for your help; one of them even offers you a starfish coin they had left over from a past vacation. They offer you a second one if you can find three numbers in your expense report that meet the same criteria.

Using the above example again, the three entries that sum to 2020 are 979, 366, and 675. Multiplying them together produces the answer, 241861950.

In your expense report, what is the product of the three entries that sum to 2020?

Your puzzle answer was 182588480.
-}

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


-- ### String cast non numbers to 0
parseContent : String -> List Int
parseContent s = map cast $ lines s

-- ### List comprehension
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
    -- ### SortedSet lives in Data.SortedSet
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
  -- ### readFile lives in System.File
  Right content <- readFile "day1i1.txt"
    -- ### Pattern Match Bind
    | Left err => printLn $ "Error while loading input: " ++ show err
  let expenses = parseContent content
  -- let expenses = testList
  putStrLn "First part"
  printLn $ findPair 2020 expenses
  putStrLn "Second part"
  printLn $ findTriplet expenses
