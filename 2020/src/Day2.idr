module Day2

import Data.Vect
import Data.Strings
import Data.List
import Data.DPair
import System.File


PasswordList : Type
PasswordList = List (Nat, Nat, Char, String)

testInput : PasswordList
testInput =
  [ (1,3,'a',"abcde")
  , (1,3,'b',"cdefg")
  , (2,9,'c',"ccccccccc")
  ]

namespace Parsing
  export
  parseLine : String -> Maybe (Nat, Nat, Char, String)
  parseLine l = do
    let [range, chr, pwd] = words l
                  | other => Nothing
    let [c,':'] = unpack chr
         | other => Nothing
    let (n,m) = Data.Strings.break (=='-') range
    Just (stringToNatOrZ n,stringToNatOrZ (strSubstr 1 (strLength m) m),c,pwd)

  export
  parseContent : String -> PasswordList
  parseContent s = mapMaybe parseLine $ lines s


namespace FirstPart
  correct : (Nat, Nat, Char, String) -> Bool
  correct (n, m, c, p) =
    -- Usage of Data.Vect: String -> (l : List Char) -> Vector (length l) Char -> (good, Vector good Char)
    let (l ** _) = filter (==c) $ fromList $ unpack p
    in n <= l && l <= m

  export
  correctPasswords : PasswordList -> Nat
  correctPasswords = go 0
    where
      go : Nat -> PasswordList -> Nat
      go c [] = c
      go c (e :: es) = go (if correct e then (c+1) else c) es

namespace SecondPart

  xor : Bool -> Bool -> Bool
  xor True False = True
  xor False True = True
  xor _ _ = False

  correct : (Nat, Nat, Char, String) -> Bool
--  correct (Z, _, _, _) = False
--  correct (_, Z, _, _) = False
  correct (S n, S m, c, p)
    = let xs = unpack p
      in case (inBounds n xs, inBounds m xs) of
          (Yes ibn, Yes ibm) => xor (index n xs == c) (index m xs == c)
          _                  => False
  correct _ = False

  export
  correctPasswords : PasswordList -> Nat
  correctPasswords xs = fst $ filter correct $ Data.Vect.fromList xs

main : IO ()
main = do
  Right content <- readFile "day2i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  -- let entries = testInput
  let entries = parseContent content
  putStrLn "First part"
  printLn $ FirstPart.correctPasswords entries
  putStrLn "Second part"
  printLn $ SecondPart.correctPasswords entries
