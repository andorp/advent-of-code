module Day7

{-
--- Day 7: Handy Haversacks ---
You land at the regional airport in time for your next flight. In fact, it looks like you'll even have time to grab some food: all flights are currently delayed due to issues in luggage processing.

Due to recent aviation regulations, many rules (your puzzle input) are being enforced about bags and their contents; bags must be color-coded and must contain specific quantities of other color-coded bags. Apparently, nobody responsible for these regulations considered how long they would take to enforce!

For example, consider the following rules:

light red bags contain 1 bright white bag, 2 muted yellow bags.
dark orange bags contain 3 bright white bags, 4 muted yellow bags.
bright white bags contain 1 shiny gold bag.
muted yellow bags contain 2 shiny gold bags, 9 faded blue bags.
shiny gold bags contain 1 dark olive bag, 2 vibrant plum bags.
dark olive bags contain 3 faded blue bags, 4 dotted black bags.
vibrant plum bags contain 5 faded blue bags, 6 dotted black bags.
faded blue bags contain no other bags.
dotted black bags contain no other bags.
These rules specify the required contents for 9 bag types. In this example, every faded blue bag is empty, every vibrant plum bag contains 11 bags (5 faded blue and 6 dotted black), and so on.

You have a shiny gold bag. If you wanted to carry it in at least one other bag, how many different bag colors would be valid for the outermost bag? (In other words: how many colors can, eventually, contain at least one shiny gold bag?)

In the above rules, the following options would be available to you:

A bright white bag, which can hold your shiny gold bag directly.
A muted yellow bag, which can hold your shiny gold bag directly, plus some other bags.
A dark orange bag, which can hold bright white and muted yellow bags, either of which could then hold your shiny gold bag.
A light red bag, which can hold bright white and muted yellow bags, either of which could then hold your shiny gold bag.
So, in this example, the number of bag colors that can eventually contain at least one shiny gold bag is 4.

How many bag colors can eventually contain at least one shiny gold bag? (The list of rules is quite long; make sure you get all of it.)

Your puzzle answer was 296.

--- Part Two ---
It's getting pretty expensive to fly these days - not because of ticket prices, but because of the ridiculous number of bags you need to buy!

Consider again your shiny gold bag and the rules from the above example:

faded blue bags contain 0 other bags.
dotted black bags contain 0 other bags.
vibrant plum bags contain 11 other bags: 5 faded blue bags and 6 dotted black bags.
dark olive bags contain 7 other bags: 3 faded blue bags and 4 dotted black bags.
So, a single shiny gold bag must contain 1 dark olive bag (and the 7 bags within it) plus 2 vibrant plum bags (and the 11 bags within each of those): 1 + 1*7 + 2 + 2*11 = 32 bags!

Of course, the actual rules have a small chance of going several levels deeper than this example; be sure to count all of the bags, even if the nesting becomes topologically impractical!

Here's another example:

shiny gold bags contain 2 dark red bags.
dark red bags contain 2 dark orange bags.
dark orange bags contain 2 dark yellow bags.
dark yellow bags contain 2 dark green bags.
dark green bags contain 2 dark blue bags.
dark blue bags contain 2 dark violet bags.
dark violet bags contain no other bags.
In this example, a single shiny gold bag must contain 126 other bags.

How many individual bags are required inside your single shiny gold bag?

Your puzzle answer was 9339.

Both parts of this puzzle are complete! They provide two gold stars: **

At this point, you should return to your Advent calendar and try another puzzle.

If you still want to see it, you can get your puzzle input.
-}

import System.File
import Data.Strings
import Data.List
import Data.SortedSet
import Data.SortedMap

-- ### Totality is important
%default total

testInput : String
testInput =
"light red bags contain 1 bright white bag, 2 muted yellow bags.\
dark orange bags contain 3 bright white bags, 4 muted yellow bags.\
bright white bags contain 1 shiny gold bag.\
muted yellow bags contain 2 shiny gold bags, 9 faded blue bags.\
shiny gold bags contain 1 dark olive bag, 2 vibrant plum bags.\
dark olive bags contain 3 faded blue bags, 4 dotted black bags.\
vibrant plum bags contain 5 faded blue bags, 6 dotted black bags.\
faded blue bags contain no other bags.\
dotted black bags contain no other bags.\
"

{-
We have a set of rules:
Rule1 :- N11 * Rule11 , ... , N1n * Rule1n
...
RuleM :- NM1 * Rule11 , ... , NM1 * RuleMn

We have look for rules which contain
Some Colour :- ... , n * Shiny Gold bag , ...
Which is represented as SomeColour -> [... , Shiny Gold , ...]
As we ignore the numbers in the lists, and we allow other elements too, but that has no information
for us to use, the search we need to do is the reverse search of tranisitive closure
-}

Bag : Type
Bag = (String, String)

data Rule : Type where
  MkRule : Bag -> List (Nat, Bag) -> Rule

Show Rule where
  show (MkRule header body) = show header ++ " :- " ++ show body

namespace Parsing

  parseBody : List String -> List (Nat, (String, String))
  parseBody [] = []
  -- ### maybe and parsePositive
  parseBody (n :: mc :: c :: bag :: rest) = (maybe 0 id $ parsePositive n, (mc, c)) :: parseBody rest
  parseBody _ = []

  parseLine : String -> Maybe Rule
  parseLine str = case words str of
    [rmc,rc,"bags","contain", "no", "other", "bags."] => Just $ MkRule (rmc, rc) []
    (rmc :: rc :: "bags" :: "contain" :: body)        => Just $ MkRule (rmc, rc) $ parseBody body
    _                                                 => Nothing

  export
  parseContent : String -> List Rule
  parseContent str = mapMaybe parseLine $ lines str

-- ### If Lazy is not used, than the creation of forever will take forever!
data Fuel = MkFuel (Lazy Fuel)

-- ### For non-primitive recursive algorithm we need a decreasing argument, which
-- shows to the type checker, there is some productivity happens in the function.
-- ### Partial functions needs to be annotated accordingly
partial
forever : Fuel
forever = MkFuel forever

namespace FirstPart

  rulesThatContainBag : List Rule -> Bag -> List Bag
  rulesThatContainBag rules bag =
    mapMaybe
      (\(MkRule h body) => if (any (\(n , b) => b == bag) body) then (Just h) else Nothing)
      rules

  partial
  bagsCanContain : List Rule -> Bag -> List Bag
  bagsCanContain rules bag = Data.SortedSet.toList $ delete bag $ go forever (singleton bag)
    where
      go : Fuel -> SortedSet Bag -> SortedSet Bag
      go (MkFuel more) bags =
        let newBags = union bags $ fromList $ concatMap (rulesThatContainBag rules)
                                            $ Data.SortedSet.toList bags
        -- TODO: This should be improved.
        in case (Data.SortedSet.toList newBags) == (Data.SortedSet.toList bags) of
            True  => bags
            False => go more newBags

  export
  partial
  noOfBagsCanContain : List Rule -> Bag -> Nat
  noOfBagsCanContain rules bag = length $ bagsCanContain rules bag

namespace SecondPart

  partial
  calculateBags : Fuel -> SortedMap Bag (List (Nat, Bag)) -> Bag -> Nat
  calculateBags (MkFuel more) bags bag = case lookup bag bags of
    Nothing => 0
    Just content => 1 + sum' (map (\(n, b) => n * calculateBags more bags b) content)

  export
  partial
  containedBags : List Rule -> Bag -> Nat
  containedBags rules bag =
    calculateBags
      forever
      (fromList (map (\(MkRule head body) => (head, body)) rules))
      bag

partial
main : IO ()
main = do
  Right content <- readFile "day7i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  -- let rules = parseContent testInput
  let rules = parseContent content
  -- putStrLn "Parser test."
  -- printLn rules
  putStrLn "First Part."
  printLn $ noOfBagsCanContain rules ("shiny","gold")
  putStrLn "Second Part."
  printLn $ the Int (cast (containedBags rules ("shiny","gold"))) - 1
