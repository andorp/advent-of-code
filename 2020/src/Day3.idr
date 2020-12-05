{-
--- Day 3: Toboggan Trajectory ---
With the toboggan login problems resolved, you set off toward the airport. While travel by toboggan might be easy, it's certainly not safe: there's very minimal steering and the area is covered in trees. You'll need to see which angles will take you near the fewest trees.

Due to the local geology, trees in this area only grow on exact integer coordinates in a grid. You make a map (your puzzle input) of the open squares (.) and trees (#) you can see. For example:

..##.......
#...#...#..
.#....#..#.
..#.#...#.#
.#...##..#.
..#.##.....
.#.#.#....#
.#........#
#.##...#...
#...##....#
.#..#...#.#
These aren't the only trees, though; due to something you read about once involving arboreal genetics and biome stability, the same pattern repeats to the right many times:

..##.........##.........##.........##.........##.........##.......  --->
#...#...#..#...#...#..#...#...#..#...#...#..#...#...#..#...#...#..
.#....#..#..#....#..#..#....#..#..#....#..#..#....#..#..#....#..#.
..#.#...#.#..#.#...#.#..#.#...#.#..#.#...#.#..#.#...#.#..#.#...#.#
.#...##..#..#...##..#..#...##..#..#...##..#..#...##..#..#...##..#.
..#.##.......#.##.......#.##.......#.##.......#.##.......#.##.....  --->
.#.#.#....#.#.#.#....#.#.#.#....#.#.#.#....#.#.#.#....#.#.#.#....#
.#........#.#........#.#........#.#........#.#........#.#........#
#.##...#...#.##...#...#.##...#...#.##...#...#.##...#...#.##...#...
#...##....##...##....##...##....##...##....##...##....##...##....#
.#..#...#.#.#..#...#.#.#..#...#.#.#..#...#.#.#..#...#.#.#..#...#.#  --->
You start on the open square (.) in the top-left corner and need to reach the bottom (below the bottom-most row on your map).

The toboggan can only follow a few specific slopes (you opted for a cheaper model that prefers rational numbers); start by counting all the trees you would encounter for the slope right 3, down 1:

From your starting position at the top-left, check the position that is right 3 and down 1. Then, check the position that is right 3 and down 1 from there, and so on until you go past the bottom of the map.

The locations you'd check in the above example are marked here with O where there was an open square and X where there was a tree:

..##.........##.........##.........##.........##.........##.......  --->
#..O#...#..#...#...#..#...#...#..#...#...#..#...#...#..#...#...#..
.#....X..#..#....#..#..#....#..#..#....#..#..#....#..#..#....#..#.
..#.#...#O#..#.#...#.#..#.#...#.#..#.#...#.#..#.#...#.#..#.#...#.#
.#...##..#..X...##..#..#...##..#..#...##..#..#...##..#..#...##..#.
..#.##.......#.X#.......#.##.......#.##.......#.##.......#.##.....  --->
.#.#.#....#.#.#.#.O..#.#.#.#....#.#.#.#....#.#.#.#....#.#.#.#....#
.#........#.#........X.#........#.#........#.#........#.#........#
#.##...#...#.##...#...#.X#...#...#.##...#...#.##...#...#.##...#...
#...##....##...##....##...#X....##...##....##...##....##...##....#
.#..#...#.#.#..#...#.#.#..#...X.#.#..#...#.#.#..#...#.#.#..#...#.#  --->
In this example, traversing the map using this slope would cause you to encounter 7 trees.

Starting at the top-left corner of your map and following a slope of right 3 and down 1, how many trees would you encounter?

--- Part Two ---
Time to check the rest of the slopes - you need to minimize the probability of a sudden arboreal stop, after all.

Determine the number of trees you would encounter if, for each of the following slopes, you start at the top-left corner and traverse the map all the way to the bottom:

Right 1, down 1.
Right 3, down 1. (This is the slope you already checked.)
Right 5, down 1.
Right 7, down 1.
Right 1, down 2.
In the above example, these slopes would find 2, 7, 3, 4, and 2 tree(s) respectively; multiplied together, these produce the answer 336.

What do you get if you multiply together the number of trees encountered on each of the listed slopes?
-}

module Day3

import Data.Strings
import System.File
import Data.Vect
import Data.List
import Data.Nat
-- ### Infinite data structures
import Data.Stream


TreeMap : Type
TreeMap = List (List Bool)

parseContent : String -> TreeMap
parseContent s = map parseLine $ lines s
  where
    parseLine : String -> List Bool
    parseLine = map (=='#') . unpack

testInput : TreeMap
testInput = parseContent $ unlines
  [ --01234567890
     "..##......."
  ,  "#...#...#.." -- 3 => .
  ,  ".#....#..#." -- 6 => X
  ,  "..#.#...#.#" -- 9 => .
  ,  ".#...##..#." -- 1 => X
  ,  "..#.##....." -- 4 => X
  ,  ".#.#.#....#" -- 7 => .
  ,  ".#........#" -- 0 => X
  ,  "#.##...#..." -- 2 => X
  ,  "#...##....#" -- 5 => X
  ,  ".#..#...#.#" -- 8 => X
  ]

namespace FirstPart
  export
  slope : TreeMap -> Maybe Nat
  slope []      = Nothing
  slope (t::ts) = go ts 3 0
    where
      go : TreeMap -> Nat -> Nat -> Maybe Nat
      go [] x noOfTrees = Just noOfTrees
      go (r :: rs) x t =
        let (S l) = length r
              | Z => Nothing
            -- ### This got veeery confusing. Don't go there. :)
            p = mod' (l + 2) x l
        in case inBounds p r of
            Yes inb => go rs (x + 3) (if (index p r) then (t + 1) else t)
            No _ => Nothing

namespace SecondPart
  -- ### My own Dec (NonEmpt xs)
  nonEmpty : (xs : List a) -> Dec (NonEmpty xs)
  nonEmpty []        = No absurd
  nonEmpty (x :: xs) = Yes IsNonEmpty

  -- So I decided to reimplement the logic as a stream based search.
  -- The complexity could be reduced with a circular buffer datatype
  slope : Nat -> Nat -> TreeMap -> Maybe Nat
  slope _     _    [] = Nothing
  slope right down ts = checkTree (drop down ts) right 0
    where
      checkTree : TreeMap -> Nat -> Nat -> Maybe Nat
      checkTree []        x c = Just c
      checkTree (t :: ts) x c = case nonEmpty t of
        Yes ne => checkTree
                    (drop down (t :: ts))
                    (x + right)
                    -- ### Cycle from Data.Stream
                    (if (index x $ cycle t) then (c + 1) else c)
        No _   => Nothing

  export
  slopes : TreeMap -> Nat
  slopes ts
    = foldl (*) 1
    $ catMaybes
    $ map (\(r,d) => slope r d ts)
      -- ### Type ~annotations with the 'the'
    $ the (List (Nat, Nat))
        [ (1,1)
        , (3,1)
        , (5,1)
        , (7,1)
        , (1,2)
        ]

namespace Parser
  parseLine : (n : Nat) -> (l : List Char) -> Maybe (Vect n Bool)
  parseLine Z     []        = Just []
  parseLine (S n) (x :: xs) = map (x=='#' ::) (parseLine n xs)
  parseLine _     _         = Nothing

  parseContent
    :  (l : List (List Char))
    -> (n : Nat)
    -> Maybe (Vect (length l) (Vect n Bool))
  parseContent l n =
    let v : ?
        v = map (parseLine n) l in
    rewrite sym $ lengthMap {f = parseLine n} l in
    sequence $ fromList v

main : IO ()
main = do
  Right content <- readFile "day3i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  -- let treeMap = testInput
  let treeMap = parseContent content
  putStrLn "First part."
  printLn $ slope treeMap
  putStrLn "Second part."
  printLn $ SecondPart.slopes treeMap

