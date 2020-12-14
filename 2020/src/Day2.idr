module Day2

{-
--- Day 2: Password Philosophy ---
Your flight departs in a few days from the coastal airport; the easiest way down to the coast from here is via toboggan.

The shopkeeper at the North Pole Toboggan Rental Shop is having a bad day. "Something's wrong with our computers; we can't log in!" You ask if you can take a look.

Their password database seems to be a little corrupted: some of the passwords wouldn't have been allowed by the Official Toboggan Corporate Policy that was in effect when they were chosen.

To try to debug the problem, they have created a list (your puzzle input) of passwords (according to the corrupted database) and the corporate policy when that password was set.

For example, suppose you have the following list:

1-3 a: abcde
1-3 b: cdefg
2-9 c: ccccccccc
Each line gives the password policy and then the password. The password policy indicates the lowest and highest number of times a given letter must appear for the password to be valid. For example, 1-3 a means that the password must contain a at least 1 time and at most 3 times.

In the above example, 2 passwords are valid. The middle password, cdefg, is not; it contains no instances of b, but needs at least 1. The first and third passwords are valid: they contain one a or nine c, both within the limits of their respective policies.

How many passwords are valid according to their policies?

Your puzzle answer was 422.

--- Part Two ---
While it appears you validated the passwords correctly, they don't seem to be what the Official Toboggan Corporate Authentication System is expecting.

The shopkeeper suddenly realizes that he just accidentally explained the password policy rules from his old job at the sled rental place down the street! The Official Toboggan Corporate Policy actually works a little differently.

Each policy actually describes two positions in the password, where 1 means the first character, 2 means the second character, and so on. (Be careful; Toboggan Corporate Policies have no concept of "index zero"!) Exactly one of these positions must contain the given letter. Other occurrences of the letter are irrelevant for the purposes of policy enforcement.

Given the same example list from above:

1-3 a: abcde is valid: position 1 contains a and position 3 does not.
1-3 b: cdefg is invalid: neither position 1 nor position 3 contains b.
2-9 c: ccccccccc is invalid: both position 2 and position 9 contain c.
How many passwords are valid according to the new interpretation of the policies?

Your puzzle answer was 451.
-}

import Data.Vect
import Data.Strings
import Data.List
import Data.DPair
import System.File


-- ### How to define a new type
PasswordList : Type
PasswordList = List (Nat, Nat, Char, String)

testInput : PasswordList
testInput =
  [ (1,3,'a',"abcde")
  , (1,3,'b',"cdefg")
  , (2,9,'c',"ccccccccc")
  ]


-- ### Namespaces for separating definitions in a file.
namespace Parsing

  -- ### Private function in a namespace
  parseLine : String -> Maybe (Nat, Nat, Char, String)
  parseLine l = do
    let [range, chr, pwd] = words l
                  | other => Nothing
    let [c,':'] = unpack chr
         | other => Nothing
    let (n,m) = Data.Strings.break (=='-') range
    Just (stringToNatOrZ n,stringToNatOrZ (strSubstr 1 (strLength m) m),c,pwd)

  -- ### Visibility, only export the name and the type, but the definition
  -- ### stays hidden.
  export
  parseContent : String -> PasswordList
  parseContent s = mapMaybe parseLine $ lines s


namespace FirstPart

  correct : (Nat, Nat, Char, String) -> Bool
  correct (n, m, c, p) =
    -- ### Data.Vector API
    -- ### Data.DPair and **
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

  -- ### I couldn't find xor.
  xor : Bool -> Bool -> Bool
  xor True False = True
  xor False True = True
  xor _ _ = False

  correct : (Nat, Nat, Char, String) -> Bool
-- !!! This seems to be an issue, compiler tells me that this is not covering.
-- !!! correct (Z, _, _, _) = False
-- !!! correct (_, Z, _, _) = False
  correct (S n, S m, c, p)
    = let xs = unpack p
      -- ### DecEq, InBounds and {auto ok : InBounds n xs}
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
