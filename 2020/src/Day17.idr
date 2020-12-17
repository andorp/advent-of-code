module Day17

{-
--- Day 17: Conway Cubes ---
As your flight slowly drifts through the sky, the Elves at the Mythical Information Bureau at the North Pole contact you. They'd like some help debugging a malfunctioning experimental energy source aboard one of their super-secret imaging satellites.

The experimental energy source is based on cutting-edge technology: a set of Conway Cubes contained in a pocket dimension! When you hear it's having problems, you can't help but agree to take a look.

The pocket dimension contains an infinite 3-dimensional grid. At every integer 3-dimensional coordinate (x,y,z), there exists a single cube which is either active or inactive.

In the initial state of the pocket dimension, almost all cubes start inactive. The only exception to this is a small flat region of cubes (your puzzle input); the cubes in this region start in the specified active (#) or inactive (.) state.

The energy source then proceeds to boot up by executing six cycles.

Each cube only ever considers its neighbors: any of the 26 other cubes where any of their coordinates differ by at most 1. For example, given the cube at x=1,y=2,z=3, its neighbors include the cube at x=2,y=2,z=2, the cube at x=0,y=2,z=3, and so on.

During a cycle, all cubes simultaneously change their state according to the following rules:

If a cube is active and exactly 2 or 3 of its neighbors are also active, the cube remains active. Otherwise, the cube becomes inactive.
If a cube is inactive but exactly 3 of its neighbors are active, the cube becomes active. Otherwise, the cube remains inactive.
The engineers responsible for this experimental energy source would like you to simulate the pocket dimension and determine what the configuration of cubes should be at the end of the six-cycle boot process.

For example, consider the following initial state:

.#.
..#
###
Even though the pocket dimension is 3-dimensional, this initial state represents a small 2-dimensional slice of it. (In particular, this initial state defines a 3x3x1 region of the 3-dimensional space.)

Simulating a few cycles from this initial state produces the following configurations, where the result of each cycle is shown layer-by-layer at each given z coordinate (and the frame of view follows the active cells in each cycle):

Starting with your given initial configuration, simulate six cycles. How many cubes are left in the active state after the sixth cycle?

Your puzzle answer was 401.

--- Part Two ---
For some reason, your simulated results don't match what the experimental energy source engineers expected. Apparently, the pocket dimension actually has four spatial dimensions, not three.

The pocket dimension contains an infinite 4-dimensional grid. At every integer 4-dimensional coordinate (x,y,z,w), there exists a single cube (really, a hypercube) which is still either active or inactive.

Each cube only ever considers its neighbors: any of the 80 other cubes where any of their coordinates differ by at most 1. For example, given the cube at x=1,y=2,z=3,w=4, its neighbors include the cube at x=2,y=2,z=3,w=3, the cube at x=0,y=2,z=3,w=4, and so on.

The initial state of the pocket dimension still consists of a small flat region of cubes. Furthermore, the same rules for cycle updating still apply: during each cycle, consider the number of active neighbors of each cube.

For example, consider the same initial state as in the example above. Even though the pocket dimension is 4-dimensional, this initial state represents a small 2-dimensional slice of it. (In particular, this initial state defines a 3x3x1x1 region of the 4-dimensional space.)

Simulating a few cycles from this initial state produces the following configurations, where the result of each cycle is shown layer-by-layer at each given z and w coordinate:

After the full six-cycle boot process completes, 848 cubes are left in the active state.

Starting with your given initial configuration, simulate six cycles in a 4-dimensional space. How many cubes are left in the active state after the sixth cycle?

Your puzzle answer was 2224.
-}

import System.File
import Data.Vect
import Data.List
import Data.SortedMap
import Data.Stream
import Debug.Trace
import Data.Strings
import Data.Nat

%default total

Coord : Nat -> Type
Coord d = Vect d Int

data State = Active | InActive

-- ### Semigroup
Semigroup State where
  InActive  <+> InActive = InActive
  _         <+> _        = Active

Show State where
  show Active   = "#"
  show InActive = "."

||| The current state of the grid is represented with the already visited coordinates and their
||| states
Grid : Nat -> Type
Grid d = SortedMap (Coord d) State

elevateGrid : Grid n -> Grid (S n)
elevateGrid g
  = fromList
  $ map (mapFst (rewrite plusCommutative 1 n in (++[0])))
  $ SortedMap.toList g

{-
When a state changes happens, we need to check apply the rules of the conway game. But as
we only store the subset of the coordinates, first we have to generate new cells of possible
candidates. And run the rules. In the extended grid, the missing elements count as Inactive one
as they are not considered as candidates for change.
-}

-- ### Interfaces for ad-hoc polymorhism.
interface Dimension (d : Nat) where
  -- ### Type level programming rulez! (Vect (pred ...)
  neighbours     : Coord d -> Vect (pred (power 3 d)) (Coord d)

-- ### This is awesome!
neighbours3 : Coord 3 -> Vect 26 (Coord 3)
neighbours3 [x,y,z] = fromList $ tail
  [ [x',y',z']
  | x' <- map (x+) [0,-1,1]
  , y' <- map (y+) [0,-1,1]
  , z' <- map (z+) [0,-1,1]
  ]

Dimension 3 where
  neighbours = neighbours3

neighbours4 : Coord 4 -> Vect 80 (Coord 4)
neighbours4 [x,y,z,w] = fromList $ tail
  [ [x',y',z',w']
  | x' <- map (x+) [0,-1,1]
  , y' <- map (y+) [0,-1,1]
  , z' <- map (z+) [0,-1,1]
  , w' <- map (w+) [0,-1,1]
  ]

Dimension 4 where
  neighbours = neighbours4

active : State -> Integer
active Active   = 1
active InActive = 0

applyRules : {d : Nat} -> (Dimension d) => Grid d -> (Coord d) -> State
applyRules g c =
  let ns = sum' $ map
            (\x => maybe 0 active (lookup x g))
            (neighbours c)
  in case lookup c g of
      Nothing       => trace "Non-existing cell" InActive
      Just Active   => if ns == 2 || ns == 3 then Active else InActive
      Just InActive => if ns == 3            then Active else InActive

-- ### Interaction between implicit parameters {} and type classes =>
evolve : {d : Nat} -> (Dimension d) => Grid d -> Grid d
evolve g =
  let activeCoords = keys g
      newCells = SortedMap.fromList
               $ concatMap
                  (\c => toList (map (\x => (x,InActive)) (neighbours c)))
                  activeCoords
      newBase = merge g newCells
  in fromList $ [ (c, applyRules newBase c) | c <- keys newBase ]

namespace Parser

  parseState : Char -> Maybe State
  parseState '.' = Just InActive
  parseState '#' = Just Active
  parseState _   = Nothing

  parseFirstLine : String -> Maybe (n ** Vect n State)
  parseFirstLine str
    = map (\l => (length l ** fromList l))
    $ traverse parseState
    $ unpack str

  parseLine : (n : Nat) -> String -> Maybe (Vect n State)
  parseLine n str = do
    xs <- traverse parseState $ unpack str
    toVect n xs

  convert : Vect m (Vect n State) -> Grid 2
  convert xss
    = fromList
    $ snd
    $ foldr (\vs , (r , ls)
             => ( r + 1
                , (snd $ foldr
                    (\s , (c , es) => (c + 1, ([r,c], s) :: es))
                    (0,[]) vs) ++ ls
                ))
            (0,[])
            xss

  export
  parseGrid : String -> Maybe (Grid 2)
  parseGrid str = do
    let ls@(x :: xs) = lines str
        | [] => Nothing
    (n ** v) <- parseFirstLine x
    vs <- traverse (parseLine n) xs
    Just $ convert (v :: fromList vs)

testInput : String
testInput =
".#.\
..#\
###
"

countActives : {d : Nat} -> Grid d -> Integer
countActives = foldr (\s , a => a + active s) 0

export
partial
solve : {d : Nat} -> (Dimension d) => Grid d -> Integer
solve g = countActives $ index 6 $ iterate evolve g

partial
main : IO ()
main = do
  Right content <- readFile "day17i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let Just grid = parseGrid content
  -- let Just grid = parseGrid testInput
      | Nothing => putStrLn "Parse error."
  printLn $ solve {d=3} $ elevateGrid grid
  printLn $ solve {d=4} $ elevateGrid $ elevateGrid grid
  pure ()
