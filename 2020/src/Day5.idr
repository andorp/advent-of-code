module Day5

{-
You board your plane only to discover a new problem: you dropped your boarding pass! You aren't sure which seat is yours, and all of the flight attendants are busy with the flood of people that suddenly made it through passport control.

You write a quick program to use your phone's camera to scan all of the nearby boarding passes (your puzzle input); perhaps you can find your seat through process of elimination.

Instead of zones or groups, this airline uses binary space partitioning to seat people. A seat might be specified like FBFBBFFRLR, where F means "front", B means "back", L means "left", and R means "right".

The first 7 characters will either be F or B; these specify exactly one of the 128 rows on the plane (numbered 0 through 127). Each letter tells you which half of a region the given seat is in. Start with the whole list of rows; the first letter indicates whether the seat is in the front (0 through 63) or the back (64 through 127). The next letter indicates which half of that region the seat is in, and so on until you're left with exactly one row.

For example, consider just the first seven characters of FBFBBFFRLR:

Start by considering the whole range, rows 0 through 127.
F means to take the lower half, keeping rows 0 through 63.
B means to take the upper half, keeping rows 32 through 63.
F means to take the lower half, keeping rows 32 through 47.
B means to take the upper half, keeping rows 40 through 47.
B keeps rows 44 through 47.
F keeps rows 44 through 45.
The final F keeps the lower of the two, row 44.
The last three characters will be either L or R; these specify exactly one of the 8 columns of seats on the plane (numbered 0 through 7). The same process as above proceeds again, this time with only three steps. L means to keep the lower half, while R means to keep the upper half.

For example, consider just the last 3 characters of FBFBBFFRLR:

Start by considering the whole range, columns 0 through 7.
R means to take the upper half, keeping columns 4 through 7.
L means to take the lower half, keeping columns 4 through 5.
The final R keeps the upper of the two, column 5.
So, decoding FBFBBFFRLR reveals that it is the seat at row 44, column 5.

Every seat also has a unique seat ID: multiply the row by 8, then add the column. In this example, the seat has ID 44 * 8 + 5 = 357.

Here are some other boarding passes:

BFFFBBFRRR: row 70, column 7, seat ID 567.
FFFBBBFRRR: row 14, column 7, seat ID 119.
BBFFBBFRLL: row 102, column 4, seat ID 820.
As a sanity check, look through your list of boarding passes. What is the highest seat ID on a boarding pass?

--- Part Two ---
Ding! The "fasten seat belt" signs have turned on. Time to find your seat.

It's a completely full flight, so your seat should be the only missing boarding pass in your list. However, there's a catch: some of the seats at the very front and back of the plane don't exist on this aircraft, so they'll be missing from your list as well.

Your seat wasn't at the very front or back, though; the seats with IDs +1 and -1 from yours will be in your list.

What is the ID of your seat?
-}

import Data.List -- (toList)
import Data.Vect
import Data.Strings
import System.File


SeatCode : Type
SeatCode = Vect 10 Char

testData : List SeatCode
testData =
  [ 'B' :: 'F' :: 'F' :: 'F' :: 'B' :: 'B' :: 'F' :: 'R' :: 'R' :: 'R' :: [] -- row 70, column 7, seat ID 567
  , 'F' :: 'F' :: 'F' :: 'B' :: 'B' :: 'B' :: 'F' :: 'R' :: 'R' :: 'R' :: [] -- row 14, column 7, seat ID 119
  , 'B' :: 'B' :: 'F' :: 'F' :: 'B' :: 'B' :: 'F' :: 'R' :: 'L' :: 'L' :: [] -- row 102, column 4, seat ID 820
  ]

namespace Parser

  parseLine : String -> Maybe SeatCode
  parseLine = go 10 . unpack
    where
      go : (n : Nat) -> List Char -> Maybe (Vect n Char)
      go Z     xs        = Just []
      go (S _) []        = Nothing
      go (S n) (x :: cs) = map (x::) (go n cs)

  export
  parseContent : String -> Maybe (List SeatCode)
  parseContent = traverse parseLine . lines

-- ### Leaving holes in parser, the code was loaded in the repl, but throw an exception runtime.
-- Warning: compiling hole Day5.Parser.{_:2381}
-- Exception: variable SystemC-45Info-isWindows is not bound

namespace FirstPart

  -- ??? How to implement the certified version of this function ???
  -- Properties
  --  * 2^^(n + 1) == (h - l)
  --  * l <= h
  export
  partition: (Char -> Bool) -> Int -> Int -> Vect (S n) Char -> Int
  partition first l h (c :: []) = case first c of
    True  => l
    False => h
  -- ### How to use pattern match to enforce (S n) property in the recursive call.
  -- ### When this property does not hold, we get kind of misterious error messages
  --     which wasn't that helpful. Probably need to train my intuition more.
  partition first l h (c :: c1 :: cs) =
    let m : Int
        m = l + ((h - l) `div` 2)
    in case first c of
      True  => partition first l       m (c1 :: cs)
      False => partition first (m + 1) h (c1 :: cs)

  bspFB : Vect 7 Char -> Int
  bspFB = partition (=='F') 0 127

  bspLR : Vect 3 Char -> Int
  bspLR = partition (=='L') 0 7

  export
  seatID : SeatCode -> Int
  seatID c =
    let rowCol : (Vect 7 Char, Vect 3 Char)
        rowCol = splitAt 7 c
    in (bspFB (fst rowCol)) * 8 + bspLR (snd rowCol)

  export
  highestSeatId : List SeatCode -> Int
  highestSeatId = foldl max 0 . map seatID

namespace SecondPart

  findMissing : List Int -> Maybe Int
  findMissing []  = Nothing
  findMissing [s] = Nothing
  findMissing (s1 :: s2 :: xs) = case s1 + 1 == s2 of
    True  => findMissing (s2 :: xs)
    False => Just (s1 + 1)

  export
  findSeat : List SeatCode -> Maybe Int
  findSeat codes = findMissing $ sort $ map FirstPart.seatID codes

main : IO ()
main = do
  Right content <- readFile "day5i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  let Just seatCodes = parseContent content
        | Nothing => do
            putStrLn "Parsing has failed."
            pure ()
  -- let seatCodes = testData
  putStrLn "First part."
  printLn $ highestSeatId seatCodes
  putStrLn "Second part."
  printLn $ findSeat seatCodes
  pure ()
