module Day11

{-
--- Day 11: Seating System ---
Your plane lands with plenty of time to spare. The final leg of your journey is a ferry that goes directly to the tropical island where you can finally start your vacation. As you reach the waiting area to board the ferry, you realize you're so early, nobody else has even arrived yet!

By modeling the process people use to choose (or abandon) their seat in the waiting area, you're pretty sure you can predict the best place to sit. You make a quick map of the seat layout (your puzzle input).

The seat layout fits neatly on a grid. Each position is either floor (.), an empty seat (L), or an occupied seat (#). For example, the initial seat layout might look like this:

L.LL.LL.LL
LLLLLLL.LL
L.L.L..L..
LLLL.LL.LL
L.LL.LL.LL
L.LLLLL.LL
..L.L.....
LLLLLLLLLL
L.LLLLLL.L
L.LLLLL.LL

Now, you just need to model the people who will be arriving shortly. Fortunately, people are entirely predictable and always follow a simple set of rules. All decisions are based on the number of occupied seats adjacent to a given seat (one of the eight positions immediately up, down, left, right, or diagonal from the seat). The following rules are applied to every seat simultaneously:

If a seat is empty (L) and there are no occupied seats adjacent to it, the seat becomes occupied.
If a seat is occupied (#) and four or more seats adjacent to it are also occupied, the seat becomes empty.
Otherwise, the seat's state does not change.
Floor (.) never changes; seats don't move, and nobody sits on the floor.

After one round of these rules, every seat in the example layout becomes occupied:

#.##.##.##
#######.##
#.#.#..#..
####.##.##
#.##.##.##
#.#####.##
..#.#.....
##########
#.######.#
#.#####.##

After a second round, the seats with four or more occupied adjacent seats become empty again:

#.LL.L#.##
#LLLLLL.L#
L.L.L..L..
#LLL.LL.L#
#.LL.LL.LL
#.LLLL#.##
..L.L.....
#LLLLLLLL#
#.LLLLLL.L
#.#LLLL.##

This process continues for three more rounds:

#.#L.L#.##
#LLL#LL.L#
L.#.L..#..
#L##.##.L#
#.#L.LL.LL
#.#L#L#.##
..L.L.....
#L#L##L#L#
#.LLLLLL.L
#.#L#L#.##

At this point, something interesting happens: the chaos stabilizes and further applications of these rules cause no seats to change state! Once people stop moving around, you count 37 occupied seats.

Simulate your seating area by applying the seating rules repeatedly until no seats change state. How many seats end up occupied?

Your puzzle answer was 2494.

--- Part Two ---
As soon as people start to arrive, you realize your mistake. People don't just care about adjacent seats - they care about the first seat they can see in each of those eight directions!

Now, instead of considering just the eight immediately adjacent seats, consider the first seat in each of those eight directions. For example, the empty seat below would see eight occupied seats:

.......#.
...#.....
.#.......
.........
..#L....#
....#....
.........
#........
...#.....
The leftmost empty seat below would only see one empty seat, but cannot see any of the occupied ones:

.............
.L.L.#.#.#.#.
.............
The empty seat below would see no occupied seats:

.##.##.
#.#.#.#
##...##
...L...
##...##
#.#.#.#
.##.##.
Also, people seem to be more tolerant than you expected: it now takes five or more visible occupied seats for an occupied seat to become empty (rather than four or more from the previous rules). The other rules still apply: empty seats that see no occupied seats become occupied, seats matching no rule don't change, and floor never changes.

Given the same starting layout as above, these new rules cause the seating area to shift around as follows:

L.LL.LL.LL
LLLLLLL.LL
L.L.L..L..
LLLL.LL.LL
L.LL.LL.LL
L.LLLLL.LL
..L.L.....
LLLLLLLLLL
L.LLLLLL.L
L.LLLLL.LL

...

#.L#.L#.L#
#LLLLLL.LL
L.L.L..#..
##L#.#L.L#
L.L#.LL.L#
#.LLLL#.LL
..#.L.....
LLL###LLL#
#.LLLLL#.L
#.L#LL#.L#
Again, at this point, people stop shifting around and the seating area reaches equilibrium. Once this occurs, you count 26 occupied seats.

Given the new visibility method and the rule change for occupied seats becoming empty, once equilibrium is reached, how many seats end up occupied?

Your puzzle answer was 2306.

Both parts of this puzzle are complete! They provide two gold stars: **

At this point, you should return to your Advent calendar and try another puzzle.
-}

import System.File
import Data.Vect
import Data.Nat
import Data.Stream
import Data.List
import Data.Strings
import Debug.Trace -- ### There is a nice working debug trace

%default total

testInput : String
testInput =
"L.LL.LL.LL\
LLLLLLL.LL\
L.L.L..L..\
LLLL.LL.LL\
L.LL.LL.LL\
L.LLLLL.LL\
..L.L.....\
LLLLLLLLLL\
L.LLLLLL.L\
L.LLLLL.LL\
"

data Space
  = Floor
  | Empty
  | Occupied
  | None

Eq Space where
  Floor     == Floor    = True
  Empty     == Empty    = True
  Occupied  == Occupied = True
  None      == None     = True
  _         == _        = False

Show Space where
  show Floor    = "."
  show Empty    = "L"
  show Occupied = "#"
  show None     = "?"

-- ### Functions that return types.
Grid : Nat -> Nat -> Type
Grid r c = Vect r (Vect c Space)

namespace Grid

  -- ### When index is used it should be notated as implicit parameters, otherwise they
  -- will be considered with 0 quantity.
  export
  get :  {r , c : Nat}
      -> (y : Fin r)
      -> (x : Fin c)
      -> Grid r c
      -> Space
  get y x g = index x $ index y g

  charOfSpace : Space -> Char
  charOfSpace Floor     = '.'
  charOfSpace Empty     = 'L'
  charOfSpace Occupied  = '#'
  charOfSpace None      = '?'

  export
  renderGrid : Grid r c -> String
  renderGrid g = unlines $ map (pack . map charOfSpace . toList) $ toList g


namespace Parser

  parseChar : Char -> Space
  parseChar c = case c of
    '.' => Floor
    'L' => Empty
    '#' => Occupied
    _   => None

  parseFirstLine : (l : List Char) -> Vect (length l) Space
  parseFirstLine l = map parseChar $ fromList l

  parseLine : (n : Nat) -> (l : List Char) -> Maybe (Vect n Space)
  parseLine n l = map (map parseChar) (toVect n l)

  export
  -- ### This is very neat! Depedent pair and function application in the type creation
  parseGrid : String -> Maybe (rc : (Nat, Nat) ** (uncurry Grid rc)) -- Produces: Grid r c
  parseGrid str = case map unpack (lines str) of
    [] => Nothing
    (l :: ls) =>
      let c : Nat
          c = length l
          pl : Vect c Space
          pl = parseFirstLine l
      in case mapMaybe (parseLine c) (fromList ls) of
          (r ** vs) => Just ((S r,c) ** (pl :: vs))


pred : Fin n -> Maybe (Fin n)
pred FZ     = Nothing
pred (FS s) = Just $ weaken s

suc : {n : Nat} -> Fin n -> Maybe (Fin n)
suc s = either (const Nothing) Just $ strengthen (FS s)

-- ### Infinite Streams are nice!
namespace Stream
  export
  diff : Stream a -> Stream (a,a)
  diff (x::y::xs) = (x,y) :: diff (y::xs)

  export
  partial
  -- ### Partial because (const False) is not a producing Stream
  find : (a -> Bool) -> Stream a -> a
  find p (x :: xs) = if p x then x else find p xs

-- First part

Neighbors : Type
Neighbors = List Space

-- ### Complicated types are 'Type's
CalcNeighbors : Type
CalcNeighbors = {r , c : Nat} -> (y : Fin r) -> (x : Fin c) -> Grid r c -> Neighbors

OccupiedLimit : Type
OccupiedLimit = Nat

namespace FirstPart

  export
  neighbors : CalcNeighbors
  neighbors y x g
    = map (\(y , x) => get y x g)
    $ the (List (Fin r, Fin c)) -- ### Extensive use of 'the' which fixes the type.
    $ Data.List.catMaybes
      [ [| (pred y , pred x) |] -- ### Another eye-candy equivalent to (,) <$> pred y <*> pred x
      , [| (pred y , Just x) |]
      , [| (pred y , suc  x) |]
      , [| (Just y , pred x) |]
      , [| (Just y , suc  x) |]
      , [| (suc  y , pred x) |]
      , [| (suc  y , Just x) |]
      , [| (suc  y , suc  x) |]
      ]

namespace SecondPart
  -- ### Type definitions in Namespaces
  data Direction = Inc | Keep | Dec

  moveCoord : {n : Nat} -> Direction -> Fin n -> Maybe (Fin n)
  moveCoord Inc  n = suc n
  moveCoord Keep n = Just n
  moveCoord Dec  n = pred n

  -- Returns the first occupied OR free seat, if the edge is reached Nothing is returned
  partial -- TODO: If we give Keep, Stay as direction this will not terminate
  seatInSight
    :  {r , c : Nat}
    -> (Direction, Fin r)
    -> (Direction, Fin c)
    -> Grid r c
    -> Maybe Space
  seatInSight {r} {c} (dy, y) (dx, x) g = do
    y' <- moveCoord dy y
    x' <- moveCoord dx x
    case get y' x' g of
      Floor    => seatInSight (dy,y') (dx,x') g
      Empty    => Just Empty
      Occupied => Just Occupied
      None     => Nothing

  export
  partial
  seatsInSight : CalcNeighbors
  seatsInSight y x g = catMaybes
    [ seatInSight (Dec ,y) (Dec ,x) g
    , seatInSight (Dec ,y) (Keep,x) g
    , seatInSight (Dec ,y) (Inc ,x) g
    , seatInSight (Keep,y) (Dec ,x) g
    , seatInSight (Keep,y) (Inc ,x) g
    , seatInSight (Inc ,y) (Dec ,x) g
    , seatInSight (Inc ,y) (Keep,x) g
    , seatInSight (Inc ,y) (Inc ,x) g
    ]

namespace Simulation
  ||| Count the number of occupied spaces
  countOccupied : Neighbors -> Nat
  countOccupied n = length $ filter (==Occupied) n

  rule : OccupiedLimit -> Space -> Neighbors -> Space
  rule _ None  _ = None
  rule _ Floor _ = Floor
  rule _ Empty    n = if countOccupied n == 0 then Occupied else Empty
  rule o Occupied n = if countOccupied n >= o then Empty else Occupied

  change : {r , c : Nat} -> (OccupiedLimit, CalcNeighbors) -> Grid r c -> Grid r c
  change {r} {c} (occLimit, calcNeighbors) g =
    zipWith
      (\row , v =>
        zipWith
          (\col => flip (rule occLimit) (calcNeighbors row col g))
          (the (Vect c (Fin c)) range) -- ### Extensive use of the explicit type annotation.
          (the (Vect c Space) v))
      (the (Vect r (Fin r)) range)
      (the (Grid r c) g)

  partial
  noChanges : {r , c : Nat} -> (OccupiedLimit, CalcNeighbors) -> Grid r c -> Grid r c
  noChanges cn g = fst $ find (uncurry (==)) $ diff $ iterate (change cn) g

  export
  partial
  showChanges : {r , c : Nat} -> (OccupiedLimit, CalcNeighbors) -> Grid r c -> List String
  showChanges ng g
    = map (renderGrid . fst)
    $ takeUntil (uncurry (==))
    $ diff
    $ iterate (change ng) g

  export
  partial
  countOccupiedSeats : {r , c : Nat} -> (OccupiedLimit, CalcNeighbors) -> Grid r c -> Nat
  countOccupiedSeats ng g =
    concatMap
      (concatMap (\x => case x of
        Occupied => 1
        _        => 0))
      (noChanges ng g)

partial
main : IO ()
main = do
  Right content <- readFile "day11i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
--  let Just ((r,c) ** grid) = parseGrid testInput
  let Just ((r,c) ** grid) = parseGrid content
      | Nothing => putStrLn "Parse error."

  putStrLn "First part."
  printLn $ countOccupiedSeats (4,neighbors) grid

  putStrLn "Second part."
  printLn $ countOccupiedSeats (5,seatsInSight) grid
