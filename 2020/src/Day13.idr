module Day13

{-
--- Day 13: Shuttle Search ---
Your ferry can make it safely to a nearby port, but it won't get much further. When you call to book another ship, you discover that no ships embark from that port to your vacation island. You'll need to get from the port to the nearest airport.

Fortunately, a shuttle bus service is available to bring you from the sea port to the airport! Each bus has an ID number that also indicates how often the bus leaves for the airport.

Bus schedules are defined based on a timestamp that measures the number of minutes since some fixed reference point in the past. At timestamp 0, every bus simultaneously departed from the sea port. After that, each bus travels to the airport, then various other locations, and finally returns to the sea port to repeat its journey forever.

The time this loop takes a particular bus is also its ID number: the bus with ID 5 departs from the sea port at timestamps 0, 5, 10, 15, and so on. The bus with ID 11 departs at 0, 11, 22, 33, and so on. If you are there when the bus departs, you can ride that bus to the airport!

Your notes (your puzzle input) consist of two lines. The first line is your estimate of the earliest timestamp you could depart on a bus. The second line lists the bus IDs that are in service according to the shuttle company; entries that show x must be out of service, so you decide to ignore them.

To save time once you arrive, your goal is to figure out the earliest bus you can take to the airport. (There will be exactly one such bus.)

For example, suppose you have the following notes:

939
7,13,x,x,59,x,31,19
Here, the earliest timestamp you could depart is 939, and the bus IDs in service are 7, 13, 59, 31, and 19. Near timestamp 939, these bus IDs depart at the times marked D:

time   bus 7   bus 13  bus 59  bus 31  bus 19
929      .       .       .       .       .
930      .       .       .       D       .
931      D       .       .       .       D
932      .       .       .       .       .
933      .       .       .       .       .
934      .       .       .       .       .
935      .       .       .       .       .
936      .       D       .       .       .
937      .       .       .       .       .
938      D       .       .       .       .
939      .       .       .       .       .
940      .       .       .       .       .
941      .       .       .       .       .
942      .       .       .       .       .
943      .       .       .       .       .
944      .       .       D       .       .
945      D       .       .       .       .
946      .       .       .       .       .
947      .       .       .       .       .
948      .       .       .       .       .
949      .       D       .       .       .
The earliest bus you could take is bus ID 59. It doesn't depart until timestamp 944, so you would need to wait 944 - 939 = 5 minutes before it departs. Multiplying the bus ID by the number of minutes you'd need to wait gives 295.

What is the ID of the earliest bus you can take to the airport multiplied by the number of minutes you'll need to wait for that bus?

Your puzzle answer was 6568.

--- Part Two ---
The shuttle company is running a contest: one gold coin for anyone that can find the earliest timestamp such that the first bus ID departs at that time and each subsequent listed bus ID departs at that subsequent minute. (The first line in your input is no longer relevant.)

For example, suppose you have the same list of bus IDs as above:

7,13,x,x,59,x,31,19
An x in the schedule means there are no constraints on what bus IDs must depart at that time.

This means you are looking for the earliest timestamp (called t) such that:

Bus ID 7 departs at timestamp t.
Bus ID 13 departs one minute after timestamp t.
There are no requirements or restrictions on departures at two or three minutes after timestamp t.
Bus ID 59 departs four minutes after timestamp t.
There are no requirements or restrictions on departures at five minutes after timestamp t.
Bus ID 31 departs six minutes after timestamp t.
Bus ID 19 departs seven minutes after timestamp t.
The only bus departures that matter are the listed bus IDs at their specific offsets from t. Those bus IDs can depart at other times, and other bus IDs can depart at those times. For example, in the list above, because bus ID 19 must depart seven minutes after the timestamp at which bus ID 7 departs, bus ID 7 will always also be departing with bus ID 19 at seven minutes after timestamp t.

In this example, the earliest timestamp at which this occurs is 1068781:

time     bus 7   bus 13  bus 59  bus 31  bus 19
1068773    .       .       .       .       .
1068774    D       .       .       .       .
1068775    .       .       .       .       .
1068776    .       .       .       .       .
1068777    .       .       .       .       .
1068778    .       .       .       .       .
1068779    .       .       .       .       .
1068780    .       .       .       .       .
1068781    D       .       .       .       .
1068782    .       D       .       .       .
1068783    .       .       .       .       .
1068784    .       .       .       .       .
1068785    .       .       D       .       .
1068786    .       .       .       .       .
1068787    .       .       .       D       .
1068788    D       .       .       .       D
1068789    .       .       .       .       .
1068790    .       .       .       .       .
1068791    .       .       .       .       .
1068792    .       .       .       .       .
1068793    .       .       .       .       .
1068794    .       .       .       .       .
1068795    D       D       .       .       .
1068796    .       .       .       .       .
1068797    .       .       .       .       .
In the above example, bus ID 7 departs at timestamp 1068788 (seven minutes after t). This is fine; the only requirement on that minute is that bus ID 19 departs then, and it does.

Here are some other examples:

The earliest timestamp that matches the list 17,x,13,19 is 3417.
67,7,59,61 first occurs at timestamp 754018.
67,x,7,59,61 first occurs at timestamp 779210.
67,7,x,59,61 first occurs at timestamp 1261476.
1789,37,47,1889 first occurs at timestamp 1202161486.
However, with so many bus IDs in your list, surely the actual earliest timestamp will be larger than 100000000000000!

What is the earliest timestamp such that all of the listed bus IDs depart at offsets matching their positions in the list?

Your puzzle answer was 554865447501099.
-}

import System.File
import Data.List1
import Data.Strings
import Data.List
import Debug.Trace
import Data.DPair
import Data.Nat

%default total

traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

Entry : Type
Entry = Nat

BusId : Type
BusId = Nat

Time : Type
Time = Int

record Timetable where
  constructor MkTimetable
  time  : Time
  -- ### Subset as a dependent pair
  buses : Subset (List (Entry, BusId)) NonEmpty

Show Timetable where
  -- ### The second part of the subset has 0 quantity, it can not be observed at runtime.
  show (MkTimetable t (Element bs _)) = show (t, bs)

namespace Parser

  parseTime : String -> Maybe Time
  parseTime = parsePositive

  parseEntry : String -> Maybe (Either () BusId)
  parseEntry str = case str of
    "x" => Just (Left ())
    n   => map Right $ parsePositive n

  parseBuses : String -> List (Entry, BusId)
  parseBuses str
    = reverse
    $ snd
    $ foldl
        (\(e, res) , lane => case lane of
          Left () => (e+1, res)
          Right b => (e+1, (e, b) :: res))
        (0, [])
    $ mapMaybe parseEntry
    $ toList
    $ split (==',')
    $ str

  export
  parseTimetable : String -> Maybe Timetable
  parseTimetable cnt = case lines cnt of
    [time, buses] => case parseBuses buses of
                      (b :: bs) => Just $ MkTimetable !(parseTime time) (Element (b :: bs) IsNonEmpty)
                      _         => Nothing
    _             => Nothing

testInput : String
testInput =
"939\
7,13,x,x,59,x,31,19\
"

namespace FirstPart

  waitTime : Time -> BusId -> Time
  waitTime t b = cast b - (t `mod` (cast b))

  ||| Find the bus that has a minimum waiting time, return boths
  findMinimum : Time -> (l : List (Entry, BusId)) -> {auto 0 ok : NonEmpty l} -> (BusId, Int)
  findMinimum t ((_, b) :: bs) = foldr checkMin (b, waitTime t b) bs
    where
      checkMin : (Entry, BusId) -> (BusId, Int) -> (BusId, Int)
      checkMin (_, b1) (b0, w0) =
        let w1 = waitTime t b1
        in if w0 < w1
            then (b0,w0)
            else (b1,w1)

  export
  solve : Timetable -> Int
  solve (MkTimetable time (Element buses _))
    = uncurry (\busId , x => cast busId * x) $ findMinimum time buses

namespace SecondPart

  -- ### GCD is very slow for Nats when it comes to big numbers.
  -- ### Integers are arbitrary precision integer values.
  partial
  gcdInt : Integer -> Integer -> Integer
  gcdInt a b =
    if b == 0
      then abs a
      else gcdInt b (a `mod` b)

  partial
  modularInverse : Integer -> Integer -> Integer
  modularInverse n g = (n + mi n 1 0 g 0 1) `mod` n
    where
      mi : Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer
      mi n i g e l a = case e of
        0 => g
        _ => let o = n `div` e
             in mi e l a (n-o*e) (i-o*l) (g-o*a)

  partial
  chineseDivision : List (Integer, Integer) -> Maybe Integer
  chineseDivision ngs =
    case foldl (\n , (_, g) => if gcdInt n g == 1 then n * g else 0) 1 ngs of
      0  => Nothing
      fn => Just $
              (foldl
                (\n , (i, g) =>
                  n + i * (fn `div` g)
                        * (modularInverse g ((fn `div` g) `mod` g)))
                0 ngs)
              `mod`
              fn

  -- ### Why quot got removed from Idris?
  partial
  quot : Integer -> Integer -> Integer
  quot n m = if n < 0 then quot (n + m) m else (n `mod` m)

  export
  partial
  solve : Timetable -> Maybe Integer
  solve (MkTimetable _ (Element buses _))
    = chineseDivision
    $ map (\(e,b) => (quot (cast b - cast e) (cast b), cast b)) buses

partial
main : IO ()
main = do
  Right content <- readFile "day13i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let Just timetable = parseTimetable content
  -- let Just timetable = parseTimetable testInput
      | Nothing => putStrLn "Bad input."
  printLn timetable
  putStrLn "First part."
  printLn $ FirstPart.solve timetable
  putStrLn "Second part."
  printLn $ SecondPart.solve timetable
  pure ()
