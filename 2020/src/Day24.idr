module Day24

{-
--- Day 24: Lobby Layout ---
Your raft makes it to the tropical island; it turns out that the small crab was an excellent navigator. You make your way to the resort.

As you enter the lobby, you discover a small problem: the floor is being renovated. You can't even reach the check-in desk until they've finished installing the new tile floor.

The tiles are all hexagonal; they need to be arranged in a hex grid with a very specific color pattern. Not in the mood to wait, you offer to help figure out the pattern.

The tiles are all white on one side and black on the other. They start with the white side facing up. The lobby is large enough to fit whatever pattern might need to appear there.

A member of the renovation crew gives you a list of the tiles that need to be flipped over (your puzzle input). Each line in the list identifies a single tile that needs to be flipped by giving a series of steps starting from a reference tile in the very center of the room. (Every line starts from the same reference tile.)

Because the tiles are hexagonal, every tile has six neighbors: east, southeast, southwest, west, northwest, and northeast. These directions are given in your list, respectively, as e, se, sw, w, nw, and ne. A tile is identified by a series of these directions with no delimiters; for example, esenee identifies the tile you land on if you start at the reference tile and then move one tile east, one tile southeast, one tile northeast, and one tile east.

Each time a tile is identified, it flips from white to black or from black to white. Tiles might be flipped more than once. For example, a line like esew flips a tile immediately adjacent to the reference tile, and a line like nwwswee flips the reference tile itself.

Here is a larger example:

sesenwnenenewseeswwswswwnenewsewsw
neeenesenwnwwswnenewnwwsewnenwseswesw
seswneswswsenwwnwse
nwnwneseeswswnenewneswwnewseswneseene
swweswneswnenwsewnwneneseenw
eesenwseswswnenwswnwnwsewwnwsene
sewnenenenesenwsewnenwwwse
wenwwweseeeweswwwnwwe
wsweesenenewnwwnwsenewsenwwsesesenwne
neeswseenwwswnwswswnw
nenwswwsewswnenenewsenwsenwnesesenew
enewnwewneswsewnwswenweswnenwsenwsw
sweneswneswneneenwnewenewwneswswnese
swwesenesewenwneswnwwneseswwne
enesenwswwswneneswsenwnewswseenwsese
wnwnesenesenenwwnenwsewesewsesesew
nenewswnwewswnenesenwnesewesw
eneswnwswnwsenenwnwnwwseeswneewsenese
neswnwewnwnwseenwseesewsenwsweewe
wseweeenwnesenwwwswnew
In the above example, 10 tiles are flipped once (to black), and 5 more are flipped twice (to black, then back to white). After all of these instructions have been followed, a total of 10 tiles are black.

Go through the renovation crew's list and determine which tiles they need to flip. After all of the instructions have been followed, how many tiles are left with the black side up?

Your puzzle answer was 465.

--- Part Two ---
The tile floor in the lobby is meant to be a living art exhibit. Every day, the tiles are all flipped according to the following rules:

Any black tile with zero or more than 2 black tiles immediately adjacent to it is flipped to white.
Any white tile with exactly 2 black tiles immediately adjacent to it is flipped to black.
Here, tiles immediately adjacent means the six tiles directly touching the tile in question.

The rules are applied simultaneously to every tile; put another way, it is first determined which tiles need to be flipped, then they are all flipped at the same time.

In the above example, the number of black tiles that are facing up after the given number of days has passed is as follows:

Day 1: 15
Day 2: 12
Day 3: 25
Day 4: 14
Day 5: 23
Day 6: 28
Day 7: 41
Day 8: 37
Day 9: 49
Day 10: 37

Day 20: 132
Day 30: 259
Day 40: 406
Day 50: 566
Day 60: 788
Day 70: 1106
Day 80: 1373
Day 90: 1844
Day 100: 2208
After executing this process a total of 100 times, there would be 2208 black tiles facing up.

How many tiles will be black after 100 days?

Your puzzle answer was 4078.

Both parts of this puzzle are complete! They provide two gold stars: **
-}

import System.File
import Data.SortedSet
import Data.Strings
import Debug.Trace
import Data.Vect
import Data.List
import Data.Stream

traceIt : Show a => a -> a
traceIt x = trace (show x) x

data Dir = E | W | SE | SW | NE | NW

Show Dir where
  show E = "E"
  show W = "W"
  show SE = "Se"
  show SW = "Sw"
  show NE = "Ne"
  show NW = "Nw"

Coord : Type
Coord = (Int, Int)

||| Black tiles facing up
Grid : Type
Grid = SortedSet Coord

-- ### Interface implementation for type synonyn like definitions.
Show Grid where
  show = show . SortedSet.toList

move : Dir -> Coord -> Coord
move E  (cx, cy) = (cx + 1, cy + 0)
move W  (cx, cy) = (cx - 1, cy + 0)
move SE (cx, cy) = (cx + 1, cy + 1)
move SW (cx, cy) = (cx + 0, cy + 1)
move NE (cx, cy) = (cx + 0, cy - 1)
move NW (cx, cy) = (cx - 1, cy - 1)

walk : List Dir -> Coord
walk = foldl (flip move) (0,0)

namespace Parser

  parseDir : List Char -> List Dir
  parseDir [] = []
  parseDir ('e' :: xs) = E :: parseDir xs
  parseDir ('w' :: xs) = W :: parseDir xs
  parseDir ('s' :: 'e' :: xs) = SE :: parseDir xs
  parseDir ('s' :: 'w' :: xs) = SW :: parseDir xs
  parseDir ('n' :: 'e' :: xs) = NE :: parseDir xs
  parseDir ('n' :: 'w' :: xs) = NW :: parseDir xs
  parseDir (x :: xs) = trace "parseDir" $ parseDir xs

  export
  parseInput : String -> List (List Dir)
  parseInput str = map (parseDir . unpack) $ lines str

testInput : String
testInput =
"sesenwnenenewseeswwswswwnenewsewsw\
neeenesenwnwwswnenewnwwsewnenwseswesw\
seswneswswsenwwnwse\
nwnwneseeswswnenewneswwnewseswneseene\
swweswneswnenwsewnwneneseenw\
eesenwseswswnenwswnwnwsewwnwsene\
sewnenenenesenwsewnenwwwse\
wenwwweseeeweswwwnwwe\
wsweesenenewnwwnwsenewsenwwsesesenwne\
neeswseenwwswnwswswnw\
nenwswwsewswnenenewsenwsenwnesesenew\
enewnwewneswsewnwswenweswnenwsenwsw\
sweneswneswneneenwnewenewwneswswnese\
swwesenesewenwneswnwwneseswwne\
enesenwswwswneneswsenwnewswseenwsese\
wnwnesenesenenwwnenwsewesewsesesew\
nenewswnwewswnenesenwnesewesw\
eneswnwswnwsenenwnwnwwseeswneewsenese\
neswnwewnwnwseenwseesewsenwsweewe\
wseweeenwnesenwwwswnew\
"

namespace FirstPart

  flipTile : Grid -> List Dir -> Grid
  flipTile g ds =
    let p = walk ds
    in case contains p g of
        True  => delete p g
        False => insert p g

  export
  calcGrid : List (List Dir) -> Grid
  calcGrid = foldl flipTile empty

  export
  solve : List (List Dir) -> Nat
  solve = length . SortedSet.toList . calcGrid

namespace SecondPart

  minMax : Grid -> (Coord, Coord)
  minMax
    = (\((mx, my), (xx, xy)) => ((mx - 1, my - 1), (xx + 2, xy + 2)))
    . foldl
        (\((mnx, mny) ,(mxx, mxy)) , (cx,cy) => ((min mnx cx, min mny cy), (max mxx cx, max mxy cy)))
      (the (Coord, Coord) ((0,0), (0,0)))

  neighbours : Coord -> Vect 6 Coord
  neighbours c = map (flip move c) [E,SE,SW,W,NW,NE]

  coords : (Coord, Coord) -> List Coord
  coords ((mx, my), (xx, xy)) =
    [ (cx, cy)
    | cx <- [mx .. xx]
    , cy <- [my .. xy]
    ]

  evolve : Grid -> Grid
  evolve g
    = SortedSet.fromList
    $ List.mapMaybe (\c@(x,y) => case (contains c g, countBlackNeighbours c) of
        (True,  1) => Just c
        (True,  2) => Just c
        (False, 2) => Just c
        _          => Nothing)
    $ coords
    $ minMax g
    where
      countBlackNeighbours : Coord -> Int
      countBlackNeighbours = sum' . map (\n => if contains n g then 1 else 0) . neighbours

  export
  solve : List (List Dir) -> Nat
  solve dirs =
    let grid = calcGrid dirs
    in length $ SortedSet.toList $ index 100 $ iterate evolve grid

main : IO ()
main = do
  Right content <- readFile "day24i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  -- let input = parseInput testInput
  let input = parseInput content
  putStrLn "First part"
  printLn $ FirstPart.solve input
  putStrLn "Second part"
  printLn $ SecondPart.solve input
  pure ()
