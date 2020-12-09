module Day9

import System.File
import Data.List
import Data.Strings
import Data.SortedSet

testInput : String
testInput =
"35\
20\
15\
25\
47\
40\
62\
55\
65\
95\
102\
117\
150\
182\
127\
219\
299\
277\
309\
576
"

-- ### Check the property that the list is not empty
nonEmpty : (l : List a) -> Dec (NonEmpty l)
nonEmpty []        = No absurd
nonEmpty (x :: xs) = Yes IsNonEmpty

-- ### Parameterised record type
record ZipList a where
  constructor ZL
  lefts  : List a
  focus  : a
  rights : List a

Show a => Show (ZipList a) where
  show (ZL ls f rs) = "ZL " ++ show (reverse ls) ++ " " ++ show f ++ " " ++ show rs

-- ### Use of auto parameters: This makes nice smart constructors.
fromListCrt : (l : List a) -> {auto 0 ok : NonEmpty l} -> ZipList a
fromListCrt [] impossible
fromListCrt (x :: xs) = ZL [] x xs

stepRight : ZipList a -> Maybe (ZipList a)
stepRight (ZL _ _ []) = Nothing
stepRight (ZL ls l (r :: rs)) = Just (ZL (l::ls) r rs)

forgetOneLeft : ZipList a -> Maybe (ZipList a)
forgetOneLeft (ZL [] _ _)         = Nothing
-- ### Because of pattern match, init will be able to find the auto proof
forgetOneLeft (ZL (x :: xs) f rs) = Just $ ZL (init (x :: xs)) f rs

||| A ZipList where lefts represent the preamble set
Code : Type
Code = ZipList Int

||| Move the focus in the code, keep the preamble length invariant
moveCode : ZipList a -> Maybe (ZipList a)
moveCode zl = stepRight zl >>= forgetOneLeft

namespace Parse

  export
  parseCode : String -> List Int
  parseCode = mapMaybe parseInteger . lines

namespace FirstPart

  createCode : Nat -> List Int -> Maybe Code
  createCode p [] = Nothing
  createCode p l@(x :: xs) = do
    zl <- pure $ fromListCrt l
    foldlM (\zl' , _ => stepRight zl') zl [1..p]

  -- Something smarter
  findPair : Int -> List Int -> Maybe Int
  findPair s = go empty
    where
      -- ### SortedSet lives in Data.SortedSet
      go : SortedSet Int -> List Int -> Maybe Int
      go found [] = Nothing
      go found (x :: xs) = case contains x found of
            False => go (insert (s - x) found) xs
            True  => Just x

  export
  findInvalids : Nat -> List Int -> List Int
  findInvalids n c = go (createCode n c) []
    where
      go : Maybe Code -> List Int -> List Int
      go Nothing res = res
      go (Just c) res = case findPair (c.focus) (c.lefts) of
        Nothing => go (moveCode c) (c.focus :: res)
        Just _ => go (moveCode c) res

namespace SecondPart

  contigous : Int -> List Int -> Maybe (List Int)
  contigous n xs = go [] n xs
    where
      go : List Int -> Int -> List Int -> Maybe (List Int)
      go acc 0 [] = Just $ reverse acc
      go acc n [] = Nothing
      go acc n (x :: xs) = if (n - x == 0)
        then Just $ reverse (x :: acc)
        else if (n - x < 0)
              then Nothing
              else go (x :: acc) (n - x) xs

  export
  findContigous : Int -> Maybe Code -> Maybe (List Int)
  findContigous _ Nothing = Nothing
  findContigous n (Just c@(ZL _ x xs)) = case contigous (n - x) xs of
    Nothing => findContigous n (stepRight c)
    Just cs => Just (x :: cs)

  export
  findWeakness : Int -> Code -> Maybe Int
  findWeakness n c = do
    (x :: xs) <- findContigous n (Just c)
      | _ => Nothing
    Just ((foldl max x xs) + (foldl min x xs))

main : IO ()
main = do
  Right content <- readFile "day9i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let preamble = 25
  let code = parseCode content
  -- let code = parseCode testInput
  Yes _ <- pure $ nonEmpty code
    | _ => putStrLn "Got empty code"
  printLn code
  putStrLn "First Part."
  let [res] = findInvalids preamble code
       | other => putStrLn $ "Got more than one result: " ++ show other
  printLn res
  putStrLn "Second Part."
  printLn $ findWeakness res $ fromListCrt code
