module Day4

{-
--- Day 4: Passport Processing ---
You arrive at the airport only to realize that you grabbed your North Pole Credentials instead of your passport. While these documents are extremely similar, North Pole Credentials aren't issued by a country and therefore aren't actually valid documentation for travel in most of the world.

It seems like you're not the only one having problems, though; a very long line has formed for the automatic passport scanners, and the delay could upset your travel itinerary.

Due to some questionable network security, you realize you might be able to solve both of these problems at the same time.

The automatic passport scanners are slow because they're having trouble detecting which passports have all required fields. The expected fields are as follows:

byr (Birth Year)
iyr (Issue Year)
eyr (Expiration Year)
hgt (Height)
hcl (Hair Color)
ecl (Eye Color)
pid (Passport ID)
cid (Country ID)
Passport data is validated in batch files (your puzzle input). Each passport is represented as a sequence of key:value pairs separated by spaces or newlines. Passports are separated by blank lines.

Here is an example batch file containing four passports:

ecl:gry pid:860033327 eyr:2020 hcl:#fffffd
byr:1937 iyr:2017 cid:147 hgt:183cm

iyr:2013 ecl:amb cid:350 eyr:2023 pid:028048884
hcl:#cfa07d byr:1929

hcl:#ae17e1 iyr:2013
eyr:2024
ecl:brn pid:760753108 byr:1931
hgt:179cm

hcl:#cfa07d eyr:2025 pid:166559648
iyr:2011 ecl:brn hgt:59in
The first passport is valid - all eight fields are present. The second passport is invalid - it is missing hgt (the Height field).

The third passport is interesting; the only missing field is cid, so it looks like data from North Pole Credentials, not a passport at all! Surely, nobody would mind if you made the system temporarily ignore missing cid fields. Treat this "passport" as valid.

The fourth passport is missing two fields, cid and byr. Missing cid is fine, but missing any other field is not, so this passport is invalid.

According to the above rules, your improved system would report 2 valid passports.

Count the number of valid passports - those that have all required fields. Treat cid as optional. In your batch file, how many passports are valid?
-}

-- Load with: idris2 -p contrib Day4.idr

-- My personal objective for this day: Learn about parsing in Idris.

import System.File
import Text.Lexer
import Text.Parser
import Data.SortedMap
import Data.List



Document : Type
Document = SortedMap String String

-- ### Multiline String in Idris
testDocumentString : String
testDocumentString =
"ecl:gry pid:860033327 eyr:2020 hcl:#fffffd\
byr:1937 iyr:2017 cid:147 hgt:183cm\
\
iyr:2013 ecl:amb cid:350 eyr:2023 pid:028048884\
hcl:#cfa07d byr:1929\
\
hcl:#ae17e1 iyr:2013\
eyr:2024\
ecl:brn pid:760753108 byr:1931\
hgt:179cm\
\
hcl:#cfa07d eyr:2025 pid:166559648\
iyr:2011 ecl:brn hgt:59in"

invalidDocuments : String
invalidDocuments =
"eyr:1972 cid:100\
hcl:#18171d ecl:amb hgt:170 pid:186cm iyr:2018 byr:1926\
\
iyr:2019\
hcl:#602927 eyr:1967 hgt:170cm\
ecl:grn pid:012533040 byr:1946\

hcl:dab227 iyr:2012\
ecl:brn hgt:182cm pid:021572410 eyr:2020 byr:1992 cid:277\

hgt:59cm ecl:zzz\
eyr:2038 hcl:74454a iyr:2023\
pid:3556412378 byr:2007\
"

validDocuments : String
validDocuments =
"pid:087499704 hgt:74in ecl:grn iyr:2012 eyr:2030 byr:1980\
hcl:#623a2f\
\
eyr:2029 ecl:blu cid:129 byr:1989\
iyr:2014 pid:896056539 hcl:#a97842 hgt:165cm\
\
hcl:#888785\
hgt:164cm byr:2001 iyr:2015 cid:88\
pid:545766238 ecl:hzl\
eyr:2022\
\
iyr:2010 hgt:158cm hcl:#b6652a ecl:blu byr:1944 eyr:2021 pid:093154719\
"

testDocuments : List Document
testDocuments =
  [ fromList [("ecl","gry"), ("pid","860033327"), ("eyr","2020"), ("hcl","#fffffd"), ("byr","1937"), ("iyr","2017"), ("cid","147"), ("hgt","183cm")]
  , fromList [("iyr","2013"), ("ecl","amb"), ("cid","350"), ("eyr","2023"), ("pid","028048884"), ("hcl","#cfa07d"), ("byr","1929")]
  , fromList [("hcl","#ae17e1"), ("iyr","2013"), ("eyr","2024"), ("ecl","brn"), ("pid","760753108"), ("byr","1931"), ("hgt","179cm")]
  , fromList [("hcl","#cfa07d"), ("eyr","2025"), ("pid","166559648"), ("iyr","2011"), ("ecl","brn"), ("hgt","59in")]
  ]

allKeys : List String
allKeys = [ "byr", "ecl", "eyr", "hcl", "hgt", "iyr", "pid" ]

-- ### The whole namespace on Parsing. How to use Lexer and Parser.
namespace Parser

  data FieldKind
    = Byr
    | Iyr
    | Eyr
    | Hgt
    | Hcl
    | Ecl
    | Pid
    | Cid
    | Value
    | Space
    | Colon
    | Newline

  Show FieldKind where
    show Byr = "Byr"
    show Iyr = "Iyr"
    show Eyr = "Eyr"
    show Hgt = "Hgt"
    show Hcl = "Hcl"
    show Ecl = "Ecl"
    show Pid = "Pid"
    show Cid = "Cid"
    show Value = "Value"
    show Space = "Space"
    show Colon = "Colon"
    show Newline = "Newline"

  Eq FieldKind where
    Byr == Byr = True
    Iyr == Iyr = True
    Eyr == Eyr = True
    Hgt == Hgt = True
    Hcl == Hcl = True
    Ecl == Ecl = True
    Pid == Pid = True
    Cid == Cid = True
    Value == Value = True
    Space == Space = True
    Colon == Colon = True
    Newline == Newline = True
    _ == _ = False

  -- ### This is very nice. A function in a typeclass that computes a type...
  -- and uses the computed type in the other function.
  TokenKind FieldKind where
    TokType Byr = String
    TokType Iyr = String
    TokType Eyr = String
    TokType Hgt = String
    TokType Hcl = String
    TokType Ecl = String
    TokType Pid = String
    TokType Cid = String
    TokType Value = String
    TokType Space = ()
    TokType Colon = ()
    TokType Newline = ()

    tokValue Byr x = x
    tokValue Iyr x = x
    tokValue Eyr x = x
    tokValue Hgt x = x
    tokValue Hcl x = x
    tokValue Ecl x = x
    tokValue Pid x = x
    tokValue Cid x = x
    tokValue Value x = x
    tokValue Space _ = ()
    tokValue Colon _ = ()
    tokValue Newline _ = ()

  FieldToken : Type
  FieldToken = Token FieldKind

  -- ### Order in tokenization is important!
  fieldTokenMap : TokenMap FieldToken
  fieldTokenMap = toTokenMap
    [ (newline, Newline)
    , (is ':', Colon)
    , (exact "byr", Byr)
    , (exact "iyr", Iyr)
    , (exact "eyr", Eyr)
    , (exact "hgt", Hgt)
    , (exact "hcl", Hcl)
    , (exact "ecl", Ecl)
    , (exact "pid", Pid)
    , (exact "cid", Cid)
    , (some (alphaNum <|> is '#'), Value)
    , (spaces, Space)
    ]

  lexDocuments : String -> Maybe (List FieldToken)
  lexDocuments str = case lex fieldTokenMap str of
    (tokens,_,_, "") => Just $ map TokenData.tok tokens
    _ => Nothing

  key : Grammar FieldToken True String
  key = choice [ match Byr, match Iyr, match Eyr, match Hgt, match Hcl, match Ecl, match Pid, match Cid ]

  keyValue : Grammar FieldToken True (String,String)
  keyValue = do
    k <- key
    match Colon
    v <- match Value
    pure (k,v)

  document : Grammar FieldToken True Document
  document = do
    x <- map fst $ sepBy1' (match Space <|> match Newline) keyValue
    pure $ fromList x

  documents : Grammar FieldToken True (List Document)
  documents = sepBy1
    -- ### (>>) needs monad, not do notation.
    (do match Newline
        match Newline)
    document

  -- ### Actually this was cute. We can use ? in types and let idris elaborate it.
  -- parseDocuments : List FieldToken -> IO (Maybe (List Document))
  parseDocuments : List FieldToken -> IO ?
  parseDocuments toks = case parse documents toks of
    Right (d, ts) => do
      -- ### At some point needed some double checking, some debugging would be great.
      -- printLn $ map (\(Tok t x) => (t,x)) tokens
      pure $ Just d
    _ => pure Nothing

  export
  parseDoc : String -> IO (List Document)
  parseDoc str = do
    let Just tokens = lexDocuments str
          | Nothing => do
              putStrLn "Lexing has failed."
              pure []
    -- printLn $ map (\(Tok t x) => (t,x)) tokens
    Just docs <- parseDocuments tokens
     | Nothing => do
        putStrLn "Document parsing has failed."
        pure []
    pure docs

namespace FirstPart

  validDocument : Document -> Bool
  validDocument d = allKeys == keys (delete "cid" d)

  export
  countValidDocuments : List Document -> Nat
  countValidDocuments = length . filter validDocument

namespace SecondPart

  allTrue : List Bool -> Bool
  allTrue [] = True
  allTrue (x :: xs) = x && allTrue xs

  -- ### I am still having fun with cast!
  checkRange : Int -> Int -> String -> Bool
  checkRange l h s = let x = cast s in l <= x && x <= h

  checkHeight : String -> Bool
  checkHeight s = case unpack s of
    (c1 :: c2 :: c3 :: 'c' :: 'm' :: []) => checkRange 150 193 $ pack [c1,c2,c3]
    (i1 :: i2 :: 'i' :: 'n' :: [])       => checkRange 59 76 $ pack [i1,i2]
    _ => False

  checkHairColor : String -> Bool
  checkHairColor s = case unpack s of
    -- ### There is an isHexDigit check. I like that one.
    ('#' :: digits) => length digits == 6 && all isHexDigit digits
    _ => False

  checkEyeColor : String -> Bool
  checkEyeColor s = elem s ["amb","blu","brn","gry","grn","hzl","oth"]

  checkPasswordID : String -> Bool
  checkPasswordID s = length s == 9 && (all isDigit (unpack s))

  validDocument : Document -> Bool
  validDocument d = allTrue
    [ maybe False (checkRange 1920 2002) $ lookup "byr" d
    , maybe False (checkRange 2010 2020) $ lookup "iyr" d
    , maybe False (checkRange 2020 2030) $ lookup "eyr" d
    , maybe False checkHeight            $ lookup "hgt" d
    , maybe False checkHairColor         $ lookup "hcl" d
    , maybe False checkEyeColor          $ lookup "ecl" d
    , maybe False checkPasswordID        $ lookup "pid" d
    ]

  export
  countValidDocuments : List Document -> Nat
  countValidDocuments = length . filter validDocument

main : IO ()
main = do
  Right content <- readFile "day4i1.txt"
    | Left err => printLn $ "Error while loading input: " ++ show err
  -- let documents = testDocuments
  documents <- parseDoc content
  putStrLn "First part."
  printLn $ FirstPart.countValidDocuments documents
  putStrLn "Secont part."
  printLn $ SecondPart.countValidDocuments documents
  pure ()
