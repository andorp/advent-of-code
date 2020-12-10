module Day9

{-
--- Day 9: Encoding Error ---
With your neighbor happily enjoying their video game, you turn your attention to an open data port on the little screen in the seat in front of you.

Though the port is non-standard, you manage to connect it to your computer through the clever use of several paperclips. Upon connection, the port outputs a series of numbers (your puzzle input).

The data appears to be encrypted with the eXchange-Masking Addition System (XMAS) which, conveniently for you, is an old cypher with an important weakness.

XMAS starts by transmitting a preamble of 25 numbers. After that, each number you receive should be the sum of any two of the 25 immediately previous numbers. The two numbers will have different values, and there might be more than one such pair.

For example, suppose your preamble consists of the numbers 1 through 25 in a random order. To be valid, the next number must be the sum of two of those numbers:

26 would be a valid next number, as it could be 1 plus 25 (or many other pairs, like 2 and 24).
49 would be a valid next number, as it is the sum of 24 and 25.
100 would not be valid; no two of the previous 25 numbers sum to 100.
50 would also not be valid; although 25 appears in the previous 25 numbers, the two numbers in the pair must be different.
Suppose the 26th number is 45, and the first number (no longer an option, as it is more than 25 numbers ago) was 20. Now, for the next number to be valid, there needs to be some pair of numbers among 1-19, 21-25, or 45 that add up to it:

26 would still be a valid next number, as 1 and 25 are still within the previous 25 numbers.
65 would not be valid, as no two of the available numbers sum to it.
64 and 66 would both be valid, as they are the result of 19+45 and 21+45 respectively.
Here is a larger example which only considers the previous 5 numbers (and has a preamble of length 5):

35
20
15
25
47
40
62
55
65
95
102
117
150
182
127
219
299
277
309
576
In this example, after the 5-number preamble, almost every number is the sum of two of the previous 5 numbers; the only number that does not follow this rule is 127.

The first step of attacking the weakness in the XMAS data is to find the first number in the list (after the preamble) which is not the sum of two of the 25 numbers before it. What is the first number that does not have this property?

Your puzzle answer was 50047984.

--- Part Two ---
The final step in breaking the XMAS encryption relies on the invalid number you just found: you must find a contiguous set of at least two numbers in your list which sum to the invalid number from step 1.

Again consider the above example:

35
20
15
25
47
40
62
55
65
95
102
117
150
182
127
219
299
277
309
576
In this list, adding up all of the numbers from 15 through 40 produces the invalid number from step 1, 127. (Of course, the contiguous set of numbers in your actual list might be much longer.)

To find the encryption weakness, add together the smallest and largest number in this contiguous range; in this example, these are 15 and 47, producing 62.

What is the encryption weakness in your XMAS-encrypted list of numbers?

Your puzzle answer was 5407707.
-}

import System.File
import Data.List
import Data.Strings
import Data.SortedSet

testInput : String
testInput =
"35\
20\
15\
25\
47\
40\
62\
55\
65\
95\
102\
117\
150\
182\
127\
219\
299\
277\
309\
576
"

-- ### Check the property that the list is not empty
nonEmpty : (l : List a) -> Dec (NonEmpty l)
nonEmpty []        = No absurd
nonEmpty (x :: xs) = Yes IsNonEmpty

-- ### Parameterised record type
record ZipList a where
  constructor ZL
  lefts  : List a
  focus  : a
  rights : List a

Show a => Show (ZipList a) where
  show (ZL ls f rs) = "ZL " ++ show (reverse ls) ++ " " ++ show f ++ " " ++ show rs

-- ### Use of auto parameters: This makes nice smart constructors.
fromListCrt : (l : List a) -> {auto 0 ok : NonEmpty l} -> ZipList a
fromListCrt [] impossible
fromListCrt (x :: xs) = ZL [] x xs

stepRight : ZipList a -> Maybe (ZipList a)
stepRight (ZL _ _ []) = Nothing
stepRight (ZL ls l (r :: rs)) = Just (ZL (l::ls) r rs)

forgetOneLeft : ZipList a -> Maybe (ZipList a)
forgetOneLeft (ZL [] _ _)         = Nothing
-- ### Because of pattern match, init will be able to find the auto proof
forgetOneLeft (ZL (x :: xs) f rs) = Just $ ZL (init (x :: xs)) f rs

||| A ZipList where lefts represent the preamble set
Code : Type
Code = ZipList Int

||| Move the focus in the code, keep the preamble length invariant
moveCode : ZipList a -> Maybe (ZipList a)
moveCode zl = stepRight zl >>= forgetOneLeft

namespace Parse

  export
  parseCode : String -> List Int
  parseCode = mapMaybe parseInteger . lines

namespace FirstPart

  createCode : Nat -> List Int -> Maybe Code
  createCode p [] = Nothing
  createCode p l@(x :: xs) = do
    zl <- pure $ fromListCrt l
    foldlM (\zl' , _ => stepRight zl') zl [1..p]

  -- Something smarter
  findPair : Int -> List Int -> Maybe Int
  findPair s = go empty
    where
      -- ### SortedSet lives in Data.SortedSet
      go : SortedSet Int -> List Int -> Maybe Int
      go found [] = Nothing
      go found (x :: xs) = case contains x found of
            False => go (insert (s - x) found) xs
            True  => Just x

  export
  findInvalids : Nat -> List Int -> List Int
  findInvalids n c = go (createCode n c) []
    where
      go : Maybe Code -> List Int -> List Int
      go Nothing res = res
      go (Just c) res = case findPair (c.focus) (c.lefts) of
        Nothing => go (moveCode c) (c.focus :: res)
        Just _ => go (moveCode c) res

namespace SecondPart

  contigous : Int -> List Int -> Maybe (List Int)
  contigous n xs = go [] n xs
    where
      go : List Int -> Int -> List Int -> Maybe (List Int)
      go acc 0 [] = Just $ reverse acc
      go acc n [] = Nothing
      go acc n (x :: xs) = if (n - x == 0)
        then Just $ reverse (x :: acc)
        else if (n - x < 0)
              then Nothing
              else go (x :: acc) (n - x) xs

  export
  findContigous : Int -> Maybe Code -> Maybe (List Int)
  findContigous _ Nothing = Nothing
  findContigous n (Just c@(ZL _ x xs)) = case contigous (n - x) xs of
    Nothing => findContigous n (stepRight c)
    Just cs => Just (x :: cs)

  export
  findWeakness : Int -> Code -> Maybe Int
  findWeakness n c = do
    (x :: xs) <- findContigous n (Just c)
      | _ => Nothing
    Just ((foldl max x xs) + (foldl min x xs))

main : IO ()
main = do
  Right content <- readFile "day9i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let preamble = 25
  let code = parseCode content
  -- let code = parseCode testInput
  Yes _ <- pure $ nonEmpty code
    | _ => putStrLn "Got empty code"
  printLn code
  putStrLn "First Part."
  let [res] = findInvalids preamble code
       | other => putStrLn $ "Got more than one result: " ++ show other
  printLn res
  putStrLn "Second Part."
  printLn $ findWeakness res $ fromListCrt code
