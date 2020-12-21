module Day21

{-
--- Day 21: Allergen Assessment ---
You reach the train's last stop and the closest you can get to your vacation island without getting wet. There aren't even any boats here, but nothing can stop you now: you build a raft. You just need a few days' worth of food for your journey.

You don't speak the local language, so you can't read any ingredients lists. However, sometimes, allergens are listed in a language you do understand. You should be able to use this information to determine which ingredient contains which allergen and work out which foods are safe to take with you on your trip.

You start by compiling a list of foods (your puzzle input), one food per line. Each line includes that food's ingredients list followed by some or all of the allergens the food contains.

Each allergen is found in exactly one ingredient. Each ingredient contains zero or one allergen. Allergens aren't always marked; when they're listed (as in (contains nuts, shellfish) after an ingredients list), the ingredient that contains each listed allergen will be somewhere in the corresponding ingredients list. However, even if an allergen isn't listed, the ingredient that contains that allergen could still be present: maybe they forgot to label it, or maybe it was labeled in a language you don't know.

For example, consider the following list of foods:

mxmxvkd kfcds sqjhc nhms (contains dairy, fish)
trh fvjkl sbzzf mxmxvkd (contains dairy)
sqjhc fvjkl (contains soy)
sqjhc mxmxvkd sbzzf (contains fish)
The first food in the list has four ingredients (written in a language you don't understand): mxmxvkd, kfcds, sqjhc, and nhms. While the food might contain other allergens, a few allergens the food definitely contains are listed afterward: dairy and fish.

The first step is to determine which ingredients can't possibly contain any of the allergens in any food in your list. In the above example, none of the ingredients kfcds, nhms, sbzzf, or trh can contain an allergen. Counting the number of times any of these ingredients appear in any ingredients list produces 5: they all appear once each except sbzzf, which appears twice.

Determine which ingredients cannot possibly contain any of the allergens in your list. How many times do any of those ingredients appear?

Your puzzle answer was 2265.

--- Part Two ---
Now that you've isolated the inert ingredients, you should have enough information to figure out which ingredient contains which allergen.

In the above example:

mxmxvkd contains dairy.
sqjhc contains fish.
fvjkl contains soy.
Arrange the ingredients alphabetically by their allergen and separate them by commas to produce your canonical dangerous ingredient list. (There should not be any spaces in your canonical dangerous ingredient list.) In the above example, this would be mxmxvkd,sqjhc,fvjkl.

Time to stock your raft with supplies. What is your canonical dangerous ingredient list?

Your puzzle answer was dtb,zgk,pxr,cqnl,xkclg,xtzh,jpnv,lsvlx.
-}

import System.File
import Data.SortedSet
import Data.SortedMap
import Data.List
import Data.List1
import Data.Strings
import Data.Nat
import Debug.Trace
import Control.Monad.Identity
import Data.Maybe


traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

Ingredient : Type
Ingredient = String

Allergen : Type
Allergen = String

Recipe : Type
Recipe = List Ingredient

record Model where
  constructor MkModel
  ingredients : SortedMap Ingredient (SortedSet Allergen)
  allergens   : SortedMap Allergen   (List Recipe)
  recipes     : List Recipe

Semigroup Model where
  (MkModel i1 a1 r1) <+> (MkModel i2 a2 r2) = MkModel (i1 <+> i2) (a1 <+> a2) (r1 <+> r2)

Monoid Model where
  neutral = MkModel neutral neutral neutral

Show Model where
  show (MkModel i a r) = "MkModel " ++ show (map SortedSet.toList i) ++ " " ++ show a ++ " " ++ show r

testData : List (List Ingredient, List Allergen)
testData =
  [ ( [ "mxmxvkd", "kfcds", "sqjhc", "nhms"], [ "dairy", "fish" ] )
  , ( [ "trh", "fvjkl", "sbzzf", "mxmxvkd"] , [ "dairy" ] )
  , ( [ "sqjhc", "fvjkl"]                   , [ "soy" ] )
  , ( [ "sqjhc", "mxmxvkd", "sbzzf"]        , [ "fish" ] )
  ]

namespace Parser

  parseLine : String -> (List Ingredient, List Allergen)
  parseLine str = mapSnd (drop 1) $ break (=="contains") $ map (pack . filter isAlpha . unpack) $ words str

  makeModel : (List Ingredient, List Allergen) -> Model
  makeModel (is, as)
    = MkModel
        (fromList [ (i, fromList as) | i <- is ])
        (fromList [ (a, [is])        | a <- as ])
        [is]

  cleanModel : Model -> Model
  cleanModel = record { recipes $= filter (/=[]) }

  export
  testInput : Model
  testInput = concatMap makeModel testData

  export
  readInput : String -> Model
  readInput str
    = concatMap (makeModel . parseLine)
    $ toList
    $ split (==')')
    $ str

namespace FirstPart

  impossibleAller : Model -> Ingredient -> Allergen -> SortedSet Allergen
  impossibleAller m ing a
    = SortedSet.fromList
    $ mapMaybe (\recipe => if (elem ing recipe) then Nothing else Just a)
    $ maybe [] id
    $ SortedMap.lookup a m.allergens

  impossibleAllers : Model -> Ingredient -> SortedSet Allergen -> SortedSet Allergen
  impossibleAllers m i as = concatMap (impossibleAller m i) as

  export
  calcSafeIngredients : Model -> Model
  calcSafeIngredients m =
    record
      { ingredients
          = SortedMap.fromList
          $ map (\(ing, as) => (ing, (difference as (impossibleAllers m ing as))))
          $ SortedMap.toList
          $ m.ingredients
      } m

  export
  safeIngredients : Model -> List Ingredient
  safeIngredients m
    = mapMaybe
        (\(k,xs) => if null xs then Just k else Nothing)
    $ SortedMap.toList
    $ m.ingredients

  nonAllergens : Model -> List Ingredient -> Nat
  nonAllergens m safe =
    concatMap
      (concatMap
        (\i => if elem i safe then 1 else 0))
      (m.recipes)

  export
  solve : Model -> Nat
  solve m = nonAllergens m $ safeIngredients $ calcSafeIngredients m

namespace SecondPart

  simplify : SortedMap Ingredient (SortedSet Allergen) -> SortedMap Ingredient Allergen
  simplify = compute empty . map (mapSnd SortedSet.toList) . SortedMap.toList
    where
      compute
        :  SortedMap Ingredient Allergen
        -> List (Ingredient, List Allergen)
        -> SortedMap Ingredient Allergen
      compute assigned [] = assigned
      compute assigned xs@(_ :: _) = fromMaybe (trace "simplify found Nothing" assigned) $ do
        let (ones@(_::_), more) = partition (\(_, as) => length as == 1) xs
            | _ => Nothing
        let onesAssigned = mapMaybe (\(i,as) => case as of { [a] => Just (i,a) ; _ => Nothing }) ones
        let assigned' = mergeLeft assigned $ fromList onesAssigned
        let more' = map (mapSnd (filter (not . flip elem (map snd onesAssigned)))) more
        Just $ compute assigned' more'

  filter : (Ord k) => (v -> Bool) -> SortedMap k v -> SortedMap k v
  filter p = SortedMap.fromList . (filter (p . snd)) . SortedMap.toList

  comm : SortedMap String String -> SortedMap String String
  comm = SortedMap.fromList . map (\(a,b) => (b,a)) . SortedMap.toList

  export
  solve : Model -> IO ()
  solve m = do
    let safe = calcSafeIngredients m
    let possibleAllergens = filter (not . null) $ safe.ingredients
    printLn $ concat $ intersperse "," $ map snd $ toList $ comm $ simplify possibleAllergens


testString : String
testString =
"mxmxvkd kfcds sqjhc nhms (contains dairy, fish)\
trh fvjkl sbzzf mxmxvkd (contains dairy)\
sqjhc fvjkl (contains soy)\
sqjhc mxmxvkd sbzzf (contains fish)\
"

main : IO ()
main = do
  Right content <- readFile "day21i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let model = readInput content
  -- let model = testInput
  putStrLn "First part."
  printLn $ FirstPart.solve model
  putStrLn "Second part."
  SecondPart.solve model
