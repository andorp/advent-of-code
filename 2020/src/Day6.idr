module Day6

{-
As your flight approaches the regional airport where you'll switch to a much larger plane, customs declaration forms are distributed to the passengers.

The form asks a series of 26 yes-or-no questions marked a through z. All you need to do is identify the questions for which anyone in your group answers "yes". Since your group is just you, this doesn't take very long.

However, the person sitting next to you seems to be experiencing a language barrier and asks if you can help. For each of the people in their group, you write down the questions for which they answer "yes", one per line. For example:

abcx
abcy
abcz
In this group, there are 6 questions to which anyone answered "yes": a, b, c, x, y, and z. (Duplicate answers to the same question don't count extra; each question counts at most once.)

Another group asks for your help, then another, and eventually you've collected answers from every group on the plane (your puzzle input). Each group's answers are separated by a blank line, and within each group, each person's answers are on a single line. For example:

testInput

This list represents answers from five groups:

The first group contains one person who answered "yes" to 3 questions: a, b, and c.
The second group contains three people; combined, they answered "yes" to 3 questions: a, b, and c.
The third group contains two people; combined, they answered "yes" to 3 questions: a, b, and c.
The fourth group contains four people; combined, they answered "yes" to only 1 question, a.
The last group contains one person who answered "yes" to only 1 question, b.
In this example, the sum of these counts is 3 + 3 + 3 + 1 + 1 = 11.

For each group, count the number of questions to which anyone answered "yes". What is the sum of those counts?

Your puzzle answer was 6630.

--- Part Two ---
As you finish the last group's customs declaration, you notice that you misread one word in the instructions:

You don't need to identify the questions to which anyone answered "yes"; you need to identify the questions to which everyone answered "yes"!

Using the same example as above:

testInput

This list represents answers from five groups:

In the first group, everyone (all 1 person) answered "yes" to 3 questions: a, b, and c.
In the second group, there is no question to which everyone answered "yes".
In the third group, everyone answered yes to only 1 question, a. Since some people did not answer "yes" to b or c, they don't count.
In the fourth group, everyone answered yes to only 1 question, a.
In the fifth group, everyone (all 1 person) answered "yes" to 1 question, b.
In this example, the sum of these counts is 3 + 0 + 1 + 1 + 1 = 6.

For each group, count the number of questions to which everyone answered "yes". What is the sum of those counts?

Your puzzle answer was 3437.

-}

import System.File
import Data.SortedSet
import Data.Strings

||| Custom Declaration
|||
||| A character represents a question in the form, such as 'd'. If 'd' is answered
||| with yes it is in the Set. Only yes answered questions are interesting.
CstmDecl : Type
CstmDecl = SortedSet Char

||| A group of custom declarations
Group : Type
Group = List CstmDecl

testInput : String
testInput =
"abc\
\
a\
b\
c\
\
ab\
ac\
\
a\
a\
a\
a\
\
b"

namespace Parser

  parseLine : String -> CstmDecl
  parseLine = fromList . unpack

  formGroups : List String -> List Group
  formGroups = go [[]]
    where
      go : List Group -> List String -> List Group
      go res        []          = res
      go res        ("" :: ys)  = go (empty :: res) ys -- Add a new group on a newline.
      go (r :: res) (y  :: ys)  = go ((parseLine y :: r) :: res) ys

  export
  parseInput : String -> List Group
  parseInput = formGroups . lines

-- ### Why this is missing from the contrib?
size : SortedSet a -> Nat
size = foldl (\c , _ => c + 1) 0

namespace FirstPart

  ||| Summarise the number of Yes answers by anyone in the list of custom groups.
  export
  sumOfAnyoneYes : List Group -> Nat
  sumOfAnyoneYes = sum' . map (size . foldl union empty)

namespace SecondPart

  -- All questions from a to z are answered with yes.
  full : CstmDecl
  full = fromList $ unpack "abcdefghijklmnopqrstuvwxyz"

  ||| Summarise the number of Yes answers by everyone in the list of custom groups.
  export
  sumOfEveryoneYes : List Group -> Nat
  sumOfEveryoneYes = sum' . map (size . foldl intersection full)

main : IO ()
main = do
  Right content <- readFile "day6i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  let customGroups = parseInput content
  -- let customGroups = parseInput testInput
  putStrLn "First Part."
  printLn $ sumOfAnyoneYes customGroups
  putStrLn "Second Part."
  printLn $ sumOfEveryoneYes customGroups
