module Day12

{-
--- Day 12: Rain Risk ---
Your ferry made decent progress toward the island, but the storm came in faster than anyone expected. The ferry needs to take evasive actions!

Unfortunately, the ship's navigation computer seems to be malfunctioning; rather than giving a route directly to safety, it produced extremely circuitous instructions. When the captain uses the PA system to ask if anyone can help, you quickly volunteer.

The navigation instructions (your puzzle input) consists of a sequence of single-character actions paired with integer input values. After staring at them for a few minutes, you work out what they probably mean:

Action N means to move north by the given value.
Action S means to move south by the given value.
Action E means to move east by the given value.
Action W means to move west by the given value.
Action L means to turn left the given number of degrees.
Action R means to turn right the given number of degrees.
Action F means to move forward by the given value in the direction the ship is currently facing.
The ship starts by facing east. Only the L and R actions change the direction the ship is facing. (That is, if the ship is facing east and the next instruction is N10, the ship would move north 10 units, but would still move east if the following action were F.)

For example:

F10
N3
F7
R90
F11
These instructions would be handled as follows:

F10 would move the ship 10 units east (because the ship starts by facing east) to east 10, north 0.
N3 would move the ship 3 units north to east 10, north 3.
F7 would move the ship another 7 units east (because the ship is still facing east) to east 17, north 3.
R90 would cause the ship to turn right by 90 degrees and face south; it remains at east 17, north 3.
F11 would move the ship 11 units south to east 17, south 8.
At the end of these instructions, the ship's Manhattan distance (sum of the absolute values of its east/west position and its north/south position) from its starting position is 17 + 8 = 25.

Figure out where the navigation instructions lead. What is the Manhattan distance between that location and the ship's starting position?

Your puzzle answer was 1645.

--- Part Two ---
Before you can give the destination to the captain, you realize that the actual action meanings were printed on the back of the instructions the whole time.

Almost all of the actions indicate how to move a waypoint which is relative to the ship's position:

Action N means to move the waypoint north by the given value.
Action S means to move the waypoint south by the given value.
Action E means to move the waypoint east by the given value.
Action W means to move the waypoint west by the given value.
Action L means to rotate the waypoint around the ship left (counter-clockwise) the given number of degrees.
Action R means to rotate the waypoint around the ship right (clockwise) the given number of degrees.
Action F means to move forward to the waypoint a number of times equal to the given value.
The waypoint starts 10 units east and 1 unit north relative to the ship. The waypoint is relative to the ship; that is, if the ship moves, the waypoint moves with it.

For example, using the same instructions as above:

F10 moves the ship to the waypoint 10 times (a total of 100 units east and 10 units north), leaving the ship at east 100, north 10. The waypoint stays 10 units east and 1 unit north of the ship.
N3 moves the waypoint 3 units north to 10 units east and 4 units north of the ship. The ship remains at east 100, north 10.
F7 moves the ship to the waypoint 7 times (a total of 70 units east and 28 units north), leaving the ship at east 170, north 38. The waypoint stays 10 units east and 4 units north of the ship.
R90 rotates the waypoint around the ship clockwise 90 degrees, moving it to 4 units east and 10 units south of the ship. The ship remains at east 170, north 38.
F11 moves the ship to the waypoint 11 times (a total of 44 units east and 110 units south), leaving the ship at east 214, south 72. The waypoint stays 4 units east and 10 units south of the ship.
After these operations, the ship's Manhattan distance from its starting position is 214 + 72 = 286.

Figure out where the navigation instructions actually lead. What is the Manhattan distance between that location and the ship's starting position?

Your puzzle answer was 35292.

Both parts of this puzzle are complete! They provide two gold stars: **
-}

import System.File
import Debug.Trace
import Data.Strings
import Data.List


data Instruction
  = E Int
  | W Int
  | S Int
  | N Int
  | L Int
  | R Int
  | F Int

{-
      +y
      N
 -x W ^ E +x
      S
      -y
-}
data Orientation = East | North | West | South


record Position where
  constructor MkPosition
  x : Int
  y : Int

namespace Position

  export
  manhattamDistance : Position -> Position -> Int
  manhattamDistance p1 p2 = abs (p2.x - p1.x) + abs (p2.y - p1.y)

-- ### Parametrized record type
record Ship o where
  constructor MkShip
  orientation : o
  position : Position

namespace ShowInstances

  export
  Show Instruction where
    show (E x) = "E" ++ show x
    show (W x) = "W" ++ show x
    show (N x) = "N" ++ show x
    show (S x) = "S" ++ show x
    show (L x) = "L" ++ show x
    show (R x) = "R" ++ show x
    show (F x) = "F" ++ show x

  export
  Show Orientation where
    show East  = "East"
    show North = "North"
    show West  = "West"
    show South = "South"

namespace Parse

  parseLine : List Char -> Maybe Instruction
  parseLine ('N' :: vs) = map N $ parseInteger $ pack vs
  parseLine ('S' :: vs) = map S $ parseInteger $ pack vs
  parseLine ('E' :: vs) = map E $ parseInteger $ pack vs
  parseLine ('W' :: vs) = map W $ parseInteger $ pack vs
  parseLine ('F' :: vs) = map F $ parseInteger $ pack vs
  parseLine ['L','9','0']     = Just $ L 90
  parseLine ['L','1','8','0'] = Just $ L 180
  parseLine ['L','2','7','0'] = Just $ L 270
  parseLine ['R','9','0']     = Just $ R 90
  parseLine ['R','1','8','0'] = Just $ R 180
  parseLine ['R','2','7','0'] = Just $ R 270
  -- ### Use trace to signal that something went wrong. As Idris is Eager, probably
  -- this won't trigger heisenbugs.
  parseLine other = trace ("Invalid line: " ++ pack other) Nothing

  export
  parseInstructions : String -> List Instruction
  parseInstructions = mapMaybe (parseLine . unpack) . lines

testInput : String
testInput =
"F10\
N3\
F7\
R90\
F11
"

namespace FirstPart

  startPos : Position -> Ship Orientation
  startPos p = MkShip East p

  forward : Ship Orientation -> Int -> Ship Orientation
  forward s u = case s.orientation of
    -- ### Record update syntax
    East  => record { position.x $= (\px => px + u) } s
    North => record { position.y $= (\py => py + u) } s
    West  => record { position.x $= (\px => px - u) } s
    South => record { position.y $= (\py => py - u) } s

  turnLeft : Orientation -> Int -> Orientation
  turnLeft o u = case (o, u) of
    (East, 90)   => North
    (East, 180)  => West
    (East, 270)  => South
    (North, 90)  => West
    (North, 180) => South
    (North, 270) => East
    (West, 90)   => South
    (West, 180)  => East
    (West, 270)  => North
    (South, 90)  => East
    (South, 180) => North
    (South, 270) => West
    other => trace ("Impossible in turnLeft: " ++ show other) o

  turnRight : Orientation -> Int -> Orientation
  turnRight o u = case (o, u) of
    (East, 90)   => South
    (East, 180)  => West
    (East, 270)  => North
    (North, 90)  => East
    (North, 180) => South
    (North, 270) => West
    (West, 90)   => North
    (West, 180)  => East
    (West, 270)  => South
    (South, 90)  => West
    (South, 180) => North
    (South, 270) => East
    other => trace ("Impossible in turnRight: " ++ show other) o

  moveShip : Ship Orientation -> Instruction -> Ship Orientation
  moveShip s (F u) = forward s u
  moveShip s (E x) = record { position.x $= (\px => px + x) } s
  moveShip s (W x) = record { position.x $= (\px => px - x) } s
  moveShip s (N y) = record { position.y $= (\py => py + y) } s
  moveShip s (S y) = record { position.y $= (\py => py - y) } s
  moveShip s (L u) = record { orientation $= flip turnLeft u  } s
  moveShip s (R u) = record { orientation $= flip turnRight u } s

  export
  solution : List Instruction -> Int
  solution ins
    = manhattamDistance (MkPosition 0 0)
    $ position
    $ foldl moveShip (startPos (MkPosition 0 0))
    $ ins

namespace SecondPart

  record WayPoint where
    constructor MkWayPoint
    x : Int
    y : Int

  startPos : Position -> Ship WayPoint
  startPos = MkShip (MkWayPoint 10 1)

  forward : Ship WayPoint -> Int -> Ship WayPoint
  forward (MkShip (MkWayPoint wx wy) (MkPosition px py)) u
         = MkShip (MkWayPoint wx wy) (MkPosition (px + u * wx) (py + u * wy))

  moveLeft : Int -> WayPoint -> WayPoint
  moveLeft 90  w = record { x  = negate (w.y) , y  = w.x          } w
  moveLeft 180 w = record { x $= negate       , y $= negate       } w
  moveLeft 270 w = record { x  = w.y          , y  = negate (w.x) } w
  moveLeft other w = trace ("moveLeft: " ++ show other) w

  moveRight : Int -> WayPoint -> WayPoint
  moveRight 90  w = record { x  = w.y          , y  = negate (w.x) } w
  moveRight 180 w = record { x $= negate       , y $= negate       } w
  moveRight 270 w = record { x  = negate (w.y) , y  = w.x          } w
  moveRight other w = trace ("moveRight: " ++ show other) w

  moveWayPoint : Instruction -> WayPoint -> WayPoint
  moveWayPoint (E u) = record { x $= (\wx => wx + u) }
  moveWayPoint (W u) = record { x $= (\wx => wx - u) }
  moveWayPoint (N u) = record { y $= (\wy => wy + u) }
  moveWayPoint (S u) = record { y $= (\wy => wy - u) }
  moveWayPoint _ = id

  moveShip : Ship WayPoint -> Instruction -> Ship WayPoint
  moveShip s (F u) = forward s u
  moveShip s (L u) = record { orientation $= moveLeft  u } s
  moveShip s (R u) = record { orientation $= moveRight u } s
  moveShip s i = record { orientation $= moveWayPoint i } s

  -- TODO: This has a common structure, but I am too tired to make it abstract.
  export
  solution : List Instruction -> Int
  solution ins
    = manhattamDistance (MkPosition 0 0)
    $ position
    $ foldl moveShip (startPos (MkPosition 0 0))
    $ ins

main : IO ()
main = do
  Right content <- readFile "day12i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let instructions = parseInstructions content
  -- let instructions = parseInstructions testInput
  -- printLn instructions
  putStrLn "First Part"
  printLn $ FirstPart.solution instructions
  putStrLn "Second Part"
  printLn $ SecondPart.solution instructions
  -- ### Putting pure () at the end of the do block sometimes helps the elaboration.
  pure ()
