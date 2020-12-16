module Day16

{-
--- Day 16: Ticket Translation ---
As you're walking to yet another connecting flight, you realize that one of the legs of your re-routed trip coming up is on a high-speed train. However, the train ticket you were given is in a language you don't understand. You should probably figure out what it says before you get to the train station after the next flight.

Unfortunately, you can't actually read the words on the ticket. You can, however, read the numbers, and so you figure out the fields these tickets must have and the valid ranges for values in those fields.

You collect the rules for ticket fields, the numbers on your ticket, and the numbers on other nearby tickets for the same train service (via the airport security cameras) together into a single document you can reference (your puzzle input).

The rules for ticket fields specify a list of fields that exist somewhere on the ticket and the valid ranges of values for each field. For example, a rule like class: 1-3 or 5-7 means that one of the fields in every ticket is named class and can be any value in the ranges 1-3 or 5-7 (inclusive, such that 3 and 5 are both valid in this field, but 4 is not).

Each ticket is represented by a single line of comma-separated values. The values are the numbers on the ticket in the order they appear; every ticket has the same format. For example, consider this ticket:

.--------------------------------------------------------.
| ????: 101    ?????: 102   ??????????: 103     ???: 104 |
|                                                        |
| ??: 301  ??: 302             ???????: 303      ??????? |
| ??: 401  ??: 402           ???? ????: 403    ????????? |
'--------------------------------------------------------'
Here, ? represents text in a language you don't understand. This ticket might be represented as 101,102,103,104,301,302,303,401,402,403; of course, the actual train tickets you're looking at are much more complicated. In any case, you've extracted just the numbers in such a way that the first number is always the same specific field, the second number is always a different specific field, and so on - you just don't know what each position actually means!

Start by determining which tickets are completely invalid; these are tickets that contain values which aren't valid for any field. Ignore your ticket for now.

For example, suppose you have the following notes:

class: 1-3 or 5-7
row: 6-11 or 33-44
seat: 13-40 or 45-50

your ticket:
7,1,14

nearby tickets:
7,3,47
40,4,50
55,2,20
38,6,12
It doesn't matter which position corresponds to which field; you can identify invalid nearby tickets by considering only whether tickets contain values that are not valid for any field. In this example, the values on the first nearby ticket are all valid for at least one field. This is not true of the other three nearby tickets: the values 4, 55, and 12 are are not valid for any field. Adding together all of the invalid values produces your ticket scanning error rate: 4 + 55 + 12 = 71.

Consider the validity of the nearby tickets you scanned. What is your ticket scanning error rate?
-}

import System.File
import Data.List
import Data.List1
import Debug.Trace
import Data.Strings
import Data.SortedSet
import Data.SortedMap
import Data.Vect
import Data.DPair

traceIt : (Show a) => String -> a -> a
traceIt m x = trace (m ++ " " ++ show x) x

||| Name of a field.
Name : Type
Name = String

record Field where
  constructor MkField
  low1  : Int
  high1 : Int
  low2  : Int
  high2 : Int

Show Field where
  show (MkField l1 h1 l2 h2) = unwords ["MkField",show l1,show h1,show l2,show h2]

Ticket : Nat -> Type
Ticket n = Vect n Int

Description : Type
Description = List (String, Field)

testData : (Description, List (Ticket 3))
testData =
  ( [("class", MkField 1 3 5 7), ("row", MkField 6 11 33 44), ("seat", MkField 13 40 45 50)]
  , [ [7,3,47]
    , [40,4,50]
    , [55,2,20]
    , [38,6,12]
    ]
  )

testInput : String
testInput =
"class: 1-3 or 5-7\
row: 6-11 or 33-44\
seat: 13-40 or 45-50\
\
your ticket:\
7,1,14\
\
nearby tickets:\
7,3,47\
40,4,50\
55,2,20\
38,6,12

--- Part Two ---
Now that you've identified which tickets contain invalid values, discard those tickets entirely. Use the remaining valid tickets to determine which field is which.

Using the valid ranges for each field, determine what order the fields appear on the tickets. The order is consistent between all tickets: if seat is the third field, it is the third field on every ticket, including your ticket.

For example, suppose you have the following notes:

class: 0-1 or 4-19
row: 0-5 or 8-19
seat: 0-13 or 16-19

your ticket:
11,12,13

nearby tickets:
3,9,18
15,1,5
5,14,9
Based on the nearby tickets in the above example, the first position must be row, the second position must be class, and the third position must be seat; you can conclude that in your ticket, class is 12, row is 11, and seat is 13.

Once you work out which field is which, look for the six fields on your ticket that start with the word departure. What do you get if you multiply those six values together?
"

namespace Parser

  export
  parseRange : String -> Maybe (Int,Int)
  parseRange str = do
    let (x ::: [y]) = split (=='-') str
        | _ => trace "parseRange" Nothing
    (,) <$> parsePositive x <*> parsePositive y

  parseField : String -> Maybe (Name, Field)
  parseField str = case break (==':') str of
    (name, ranges) => case words ranges of
      [":", range1, "or", range2] => do
        (l1, h1) <- parseRange range1
        (l2, h2) <- parseRange range2
        Just (name, MkField l1 h1 l2 h2)
      _ => trace ("parseField: " ++ str) Nothing

  parseDesc : List String -> Maybe (Description, List String)
  parseDesc xs = go [] xs
    where
      go : Description -> List String -> Maybe (Description, List String)
      go d [] = Nothing
      go d ("" :: rest) = Just (reverse d, rest)
      go d (l :: rest) = do
        f <- parseField l
        go (f::d) rest

  parseTicket : String -> Maybe (n ** Ticket n)
  parseTicket l = map (\l => (length l ** fromList l)) $ traverse parseInteger $ toList $ split (==',') l

  parseTicketLength : (n : Nat) -> String -> Maybe (Ticket n)
  parseTicketLength n l = do
    numbers <- traverse parseInteger $ toList $ split (==',') l
    toVect n numbers

  -- Why (n ** Ticket n) paranthesis is needed?
  parseYourTicket : List String -> Maybe ((n ** Ticket n), List String)
  parseYourTicket ("your ticket:" :: ticket :: "" :: rest) = do
    t <- parseTicket ticket
    Just (t, rest)
  parseYourTicket _ = Nothing

  parseNearBy : (n : Nat) -> List String -> Maybe (List (Ticket n))
  parseNearBy n ("nearby tickets:" :: tickets) = do
    traverse (parseTicketLength n) tickets
  parseNearBy _ _ = Nothing

  export
  parseInput : String -> Maybe (n ** (Description, Ticket n, List (Ticket n)))
  parseInput cnt = do
    let ls = lines cnt
    (desc, secondPart) <- parseDesc ls
    ((n ** yourTicket), thirdPart) <- parseYourTicket secondPart
    nearByTickets <- parseNearBy n thirdPart
    Just (n ** (desc, yourTicket, nearByTickets))

namespace ErrorDetection

  fieldMatch : Field -> Int -> Bool
  fieldMatch (MkField l1 h1 l2 h2) i = (l1 <= i && i <= h1) || (l2 <= i && i <= h2)

  export
  matchingFields : Description -> Int -> List Name
  matchingFields d i = mapMaybe (\(n,f) => if fieldMatch f i then Just n else Nothing) d

  ||| Returns the number which mismatch at least one field
  export
  mismatch : Description -> {n : Nat} -> Ticket n -> List Int
  mismatch d ts
    = toList $ snd
    $ mapMaybe
        (\f => case matchingFields d f of
          [] => Just f
          _  => Nothing)
        ts

namespace FirstPart

  ticketScanningError : Description -> {n : Nat} -> List (Ticket n) -> Int
  ticketScanningError d ts = foldl (\acc0 , t => acc0 + foldl (+) 0 (mismatch d t)) 0 ts

  export
  solve : Description -> {n : Nat} -> List (Ticket n) -> Int
  solve = ticketScanningError

testInput2 : String
testInput2 =
"class: 0-1 or 4-19\
row: 0-5 or 8-19\
seat: 0-13 or 16-19\
\
your ticket:\
11,12,13\
\
nearby tickets:\
3,9,18\
15,1,5\
5,14,9
"

namespace SecondPart

  -- Filter out invalid nearby tickets
  -- For all the nearby tickets to a sweep, filtering out the mismatching fields
  -- Stop the search if only one possible value is associated with the field.

  keepValidTickets : Description -> {n : Nat} -> List (Ticket n) -> List (Ticket n)
  keepValidTickets d = filter (isNil . mismatch d)

  determineFields : Description -> {n : Nat} -> List (Ticket n) -> Maybe (Vect n Name)
  determineFields d ts
    = checkUniqueNames
    $ removeUnique
    $ foldl (flip crossOutNames) initValue ts
    where
      -- ### Local type definitions in where clauses
      FieldMeaning : Type
      FieldMeaning = Vect n (SortedSet Name)

      initValue : FieldMeaning
      initValue = replicate n (fromList (map fst d))

      crossOutNames : Ticket n -> FieldMeaning -> FieldMeaning
      crossOutNames = zipWith
        $ \value , names
        => intersection names (fromList (matchingFields d value))

      removeUnique : FieldMeaning -> FieldMeaning
      removeUnique names =
        let us = uniques names
            names' = map
                      -- ### It is enough to spell out part of the qualified
                      -- namespace to help the elaboration.
                      (\ns => case SortedSet.toList ns of
                        []  => trace ("removeUnique found empty." ++ show (map SortedSet.toList names)) ns
                        [u] => ns
                        _   => difference ns us)
                      names
        in if map SortedSet.toList names == map SortedSet.toList names'
              then names
              else removeUnique names'
        where
          uniques : FieldMeaning -> SortedSet Name
          uniques
            = foldl
                (\s , ns => case SortedSet.toList ns of
                  [m] => insert m s
                  _   => s)
                empty

      checkUniqueNames : FieldMeaning -> Maybe (Vect n Name)
      checkUniqueNames =
        traverse
          (\s => case SortedSet.toList s of
            [u] => Just u
            _   => Nothing)

  export
  solve : Description -> {n : Nat} -> Ticket n -> List (Ticket n) -> Maybe Int
  solve d t ts = do
    fields <- determineFields d $ keepValidTickets d ts
    Just $ product'
         $ toList
         $ zipWith
            (\name , v => if isInfixOf "departure" name then v else 1)
            fields t

  export
  test : Description -> {n : Nat} -> List (Ticket n) -> IO ()
  test d ts = do
    printLn $ determineFields d $ keepValidTickets d ts
    pure ()

main : IO ()
main = do
  Right content <- readFile "day16i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let Just (n ** (d,yt,ts)) = parseInput content
        | Nothing => putStrLn "Bad parse"
  putStrLn "First Part."
  printLn $ FirstPart.solve d ts
  putStrLn "Second Part."
  printLn $ SecondPart.solve d yt ts
