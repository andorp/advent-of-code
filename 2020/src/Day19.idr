module Day19

{-
--- Day 19: Monster Messages ---
You land in an airport surrounded by dense forest. As you walk to your high-speed train, the Elves at the Mythical Information Bureau contact you again. They think their satellite has collected an image of a sea monster! Unfortunately, the connection to the satellite is having problems, and many of the messages sent back from the satellite have been corrupted.

They sent you a list of the rules valid messages should obey and a list of received messages they've collected so far (your puzzle input).

The rules for valid messages (the top part of your puzzle input) are numbered and build upon each other. For example:

0: 1 2
1: "a"
2: 1 3 | 3 1
3: "b"
Some rules, like 3: "b", simply match a single character (in this case, b).

The remaining rules list the sub-rules that must be followed; for example, the rule 0: 1 2 means that to match rule 0, the text being checked must match rule 1, and the text after the part that matched rule 1 must then match rule 2.

Some of the rules have multiple lists of sub-rules separated by a pipe (|). This means that at least one list of sub-rules must match. (The ones that match might be different each time the rule is encountered.) For example, the rule 2: 1 3 | 3 1 means that to match rule 2, the text being checked must match rule 1 followed by rule 3 or it must match rule 3 followed by rule 1.

Fortunately, there are no loops in the rules, so the list of possible matches will be finite. Since rule 1 matches a and rule 3 matches b, rule 2 matches either ab or ba. Therefore, rule 0 matches aab or aba.

Here's a more interesting example:

0: 4 1 5
1: 2 3 | 3 2
2: 4 4 | 5 5
3: 4 5 | 5 4
4: "a"
5: "b"
Here, because rule 4 matches a and rule 5 matches b, rule 2 matches two letters that are the same (aa or bb), and rule 3 matches two letters that are different (ab or ba).

Since rule 1 matches rules 2 and 3 once each in either order, it must match two pairs of letters, one pair with matching letters and one pair with different letters. This leaves eight possibilities: aaab, aaba, bbab, bbba, abaa, abbb, baaa, or babb.

Rule 0, therefore, matches a (rule 4), then any of the eight options from rule 1, then b (rule 5): aaaabb, aaabab, abbabb, abbbab, aabaab, aabbbb, abaaab, or ababbb.

The received messages (the bottom part of your puzzle input) need to be checked against the rules so you can determine which are valid and which are corrupted. Including the rules and the messages together, this might look like:

0: 4 1 5
1: 2 3 | 3 2
2: 4 4 | 5 5
3: 4 5 | 5 4
4: "a"
5: "b"

ababbb
bababa
abbbab
aaabbb
aaaabbb
Your goal is to determine the number of messages that completely match rule 0. In the above example, ababbb and abbbab match, but bababa, aaabbb, and aaaabbb do not, producing the answer 2. The whole message must match all of rule 0; there can't be extra unmatched characters in the message. (For example, aaaabbb might appear to match rule 0 above, but it has an extra unmatched b on the end.)

How many messages completely match rule 0?

Your puzzle answer was 190.

--- Part Two ---
As you look over the list of messages, you realize your matching rules aren't quite right. To fix them, completely replace rules 8: 42 and 11: 42 31 with the following:

8: 42 | 42 8
11: 42 31 | 42 11 31
This small change has a big impact: now, the rules do contain loops, and the list of messages they could hypothetically match is infinite. You'll need to determine how these changes affect which messages are valid.

Fortunately, many of the rules are unaffected by this change; it might help to start by looking at which rules always match the same set of values and how those rules (especially rules 42 and 31) are used by the new versions of rules 8 and 11.

(Remember, you only need to handle the rules you have; building a solution that could handle any hypothetical combination of rules would be significantly more difficult.)

For example:

42: 9 14 | 10 1
9: 14 27 | 1 26
10: 23 14 | 28 1
1: "a"
11: 42 31
5: 1 14 | 15 1
19: 14 1 | 14 14
12: 24 14 | 19 1
16: 15 1 | 14 14
31: 14 17 | 1 13
6: 14 14 | 1 14
2: 1 24 | 14 4
0: 8 11
13: 14 3 | 1 12
15: 1 | 14
17: 14 2 | 1 7
23: 25 1 | 22 14
28: 16 1
4: 1 1
20: 14 14 | 1 15
3: 5 14 | 16 1
27: 1 6 | 14 18
14: "b"
21: 14 1 | 1 14
25: 1 1 | 1 14
22: 14 14
8: 42
26: 14 22 | 1 20
18: 15 15
7: 14 5 | 1 21
24: 14 1

abbbbbabbbaaaababbaabbbbabababbbabbbbbbabaaaa
bbabbbbaabaabba
babbbbaabbbbbabbbbbbaabaaabaaa
aaabbbbbbaaaabaababaabababbabaaabbababababaaa
bbbbbbbaaaabbbbaaabbabaaa
bbbababbbbaaaaaaaabbababaaababaabab
ababaaaaaabaaab
ababaaaaabbbaba
baabbaaaabbaaaababbaababb
abbbbabbbbaaaababbbbbbaaaababb
aaaaabbaabaaaaababaa
aaaabbaaaabbaaa
aaaabbaabbaaaaaaabbbabbbaaabbaabaaa
babaaabbbaaabaababbaabababaaab
aabbbbbaabbbaaaaaabbbbbababaaaaabbaaabba
Without updating rules 8 and 11, these rules only match three messages: bbabbbbaabaabba, ababaaaaaabaaab, and ababaaaaabbbaba.

However, after updating rules 8 and 11, a total of 12 messages match:

bbabbbbaabaabba
babbbbaabbbbbabbbbbbaabaaabaaa
aaabbbbbbaaaabaababaabababbabaaabbababababaaa
bbbbbbbaaaabbbbaaabbabaaa
bbbababbbbaaaaaaaabbababaaababaabab
ababaaaaaabaaab
ababaaaaabbbaba
baabbaaaabbaaaababbaababb
abbbbabbbbaaaababbbbbbaaaababb
aaaaabbaabaaaaababaa
aaaabbaabbaaaaaaabbbabbbaaabbaabaaa
aabbbbbaabbbaaaaaabbbbbababaaaaabbaaabba
After updating rules 8 and 11, how many messages completely match rule 0?

Your puzzle answer was 311.
-}

import System.File
import Data.SortedMap
import Text.Lexer
import Text.Parser
import Debug.Trace
import Data.List
import Data.Strings
import Data.Nat

traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

Message : Type
Message = String

data Occ a
  = Once a
  | Twice a a
  | Thrice a a a

Functor Occ where
  map f (Once a) = Once (f a)
  map f (Twice a1 a2) = Twice (f a1) (f a2)
  map f (Thrice a1 a2 a3) = Thrice (f a1) (f a2) (f a3)

Show a => Show (Occ a) where
  show (Once a) = "Once " ++ show a
  show (Twice a1 a2) = "Twice " ++ show a1 ++ " " ++ show a2
  show (Thrice a1 a2 a3) = "Thrice " ++ show a1 ++ " " ++ show a2 ++ " " ++ show a3

-- ### Shape functors
data Rule a
  = Match    Int Char
  | Branch   Int (Occ a)
  | OrBranch Int (Occ a) (Occ a)

Functor Rule where
  map f (Match    n c) = Match n c
  map f (Branch   n rs) = Branch n (map f rs)
  map f (OrBranch n r1 r2) = OrBranch n (map f r1) (map f r2)

Show a => Show (Rule a) where
  show (Match    n c)       = "Match "    ++ show n ++ " " ++ show c
  show (Branch   n lr)      = "Branch "   ++ show n ++ " (" ++ show lr ++ ")"
  show (OrBranch n lr1 lr2) = "OrBranch " ++ show n ++ " (" ++ show lr1 ++ ") (" ++ show lr2 ++ ")"

-- As Christmas is at the corner, we need some magic :)
namespace FunctorMagic

  -- ### Higher kinded types
  public export
  data Fix : (Type -> Type) -> Type where
    MkFix : f (Fix f) -> Fix f

  unFix : Fix f -> f (Fix f)
  unFix (MkFix f) = f

  export
  cata : (Functor f) => (f a -> a) -> (Fix f -> a)
  cata a = a . map (cata a) . unFix

  export
  ana : (Functor f) => (a -> f a) -> (a -> Fix f)
  ana ca = MkFix . (map (ana ca)) . ca


RuleSet : Type
RuleSet = SortedMap Int (Rule Int)

-- ### Fixpoint of the shape functors makes trees
RuleTree : Type
RuleTree = Fix Rule

-- Build a rule tree without sharing.
-- TODO: Implement the sharing version.
calculateRuleTree : RuleSet -> Int -> RuleTree
calculateRuleTree rs = ana build
  where
    build : Int -> Rule Int
    build n = case lookup n rs of
      Nothing => trace "calculateRuleTree.build" $ Match n '?'
      Just r  => r

namespace CodeMatcher

  -- ### This was needed as monadic decisions in the parser is not possible?
  data CodeTkn = ChrA | ChrB | Err

  Eq CodeTkn where
    ChrA == ChrA = True
    ChrB == ChrB = True
    Err == Err   = True
    _   == _     = False

  Show CodeTkn where
    show ChrA = "ChrA"
    show ChrB = "ChrB"
    show Err = "Err"

  TokenKind CodeTkn where
    TokType  ChrA = ()
    TokType  ChrB = ()
    TokType  Err  = ()
    tokValue Err  _ = ()
    tokValue ChrA _ = ()
    tokValue ChrB _ = ()

  export
  CodeToken : Type
  CodeToken = Token CodeTkn

  Show CodeToken where
    show (Tok t n) = show (t,n)

  codeTokenMap : TokenMap CodeToken
  codeTokenMap = toTokenMap
    [ (is 'a', ChrA)
    , (is 'b', ChrB)
    , (any, Err)
    ]

  lexCode : String -> Maybe (List CodeToken)
  lexCode str = case lex codeTokenMap str of
    (tokens,_,_, "")  => Just $ map TokenData.tok tokens
    _                 => Nothing

  public export
  CodeMatcher : Type
  CodeMatcher = Grammar CodeToken True ()

  -- ### User friendly API on the outside
  public export
  data RuleOverride
    = NoChange
    | Override (Occ CodeMatcher -> CodeMatcher)

  -- ### Library friendly API in the inside
  toMaybe : RuleOverride -> Maybe (Occ CodeMatcher -> CodeMatcher)
  toMaybe NoChange = Nothing
  toMaybe (Override x) = Just x

  export
  buildCodeMatcher : (Int -> RuleOverride) -> RuleTree -> CodeMatcher
  buildCodeMatcher onBranch = cata collapse
    where
      occ : Occ CodeMatcher -> CodeMatcher
      occ (Once r)          = r
      occ (Twice r1 r2)     = do r1 ; r2
      occ (Thrice r1 r2 r3) = do r1 ; r2 ; r3

      collapse : Rule CodeMatcher -> CodeMatcher
      collapse (Match n c) = case c of
        -- ### I had a hard time here. 'pure' and 'match' introduced unresolved hole error.
        -- Which was a good indication that I am not on the right track... :)
        -- The monadic decisions mentioned above...
        'a' => match ChrA
        'b' => match ChrB
        _   => fail ""
      -- ### Higher order function fun in 'maybe occ ...'
      collapse (Branch n o)       = (maybe occ id (toMaybe (onBranch n))) o
      collapse (OrBranch n o1 o2) = occ o1 <|> occ o2

  matchCode0 : CodeMatcher -> List CodeToken -> Bool
  matchCode0 matcher toks = case parse matcher toks of
    Right (d, []) => True
    _             => False

  export
  matchCode : CodeMatcher -> String -> Maybe Bool
  matchCode cm ln = do
    tokens <- lexCode ln
    Just $ matchCode0 cm tokens

namespace Parser

  parseInt : String -> Maybe Int
  parseInt s = parsePositive s

  parseRule : String -> Maybe RuleSet
  parseRule str = do
    let ws@(h :: b) = words str
        | [] => trace ("parseRule.words: " ++ show str) Nothing
    h0 <- init' $ unpack h
    hn <- parseInt $ pack h0
    case b of
      ["\"a\""]
        => Just $ SortedMap.singleton hn $ Match hn 'a'
      ["\"b\""]
        => Just $ SortedMap.singleton hn $ Match hn 'b'
      rs => map (SortedMap.singleton hn) $ case break ("|"==) rs of
        ([r1], [])
          => Just $ Branch hn (Once   !(parseInt r1))
        ([r1,r2], [])
          => Just $ Branch hn (Twice  !(parseInt r1) !(parseInt r2))
        ([r1,r2,r3], [])
          => Just $ Branch hn (Thrice !(parseInt r1) !(parseInt r2) !(parseInt r3))
        ([r1], ["|", r2])
          => Just $ OrBranch hn (Once !(parseInt r1))                  (Once !(parseInt r2))
        ([r1,r2], ["|", r3])
          => Just $ OrBranch hn (Twice !(parseInt r1) !(parseInt r2))  (Once !(parseInt r3))
        ([r1], ["|", r2, r3])
          => Just $ OrBranch hn (Once !(parseInt r1))                  (Twice !(parseInt r2) !(parseInt r3))
        ([r1,r2], ["|", r3,r4])
          => Just $ OrBranch hn (Twice !(parseInt r1) !(parseInt r2))  (Twice !(parseInt r3) !(parseInt r4))
        _ => trace ("parseRule: " ++ show rs) Nothing

  parseRules : List String -> Maybe RuleSet
  parseRules rs = map (foldl mergeLeft empty) $ traverse parseRule rs

  export
  parseInput : String -> Maybe (RuleSet, List Message)
  parseInput cnt = do
    let (rules0, (_ :: messages)) = break (=="") $ lines cnt
        | (_, []) => trace "parseInput.messages" Nothing
    rules <- parseRules rules0
    Just (rules, messages)

-- ### This should be the part of the standard lib?
count : (Foldable f) => (a -> Bool) -> f a -> Nat
count p = foldl (\a , x => if p x then (a + 1) else a) 0

namespace FirstPart

  export
  solve : (RuleSet, List Message) -> Maybe Nat
  solve (rs, messages) = do
    let ruleTree = calculateRuleTree rs 0
    let codeMatcher = buildCodeMatcher (const NoChange) ruleTree
    map (count id) $ traverse (matchCode codeMatcher) messages

namespace SecondPart

  findAlmost : Nat -> CodeMatcher -> Grammar CodeToken True (List ())
  findAlmost Z _     = fail ""
  findAlmost (S n) g = Parser.count (between 1 n) g

  changeRule0 : Int -> RuleOverride
  -- ### LambdaCase!
  changeRule0 0 = Override $ \case
    Once r            => r
    Twice r1 r2       => do r1 ; r2
    Thrice r42 _ r31  => () <$ do
      xs <- some r42
      findAlmost (length xs) r31
  changeRule0 _ = NoChange

  prepareRuleSet : RuleSet -> RuleSet
  prepareRuleSet rs
    = insert 0 (Branch 0 (Thrice 42 42 31))
    $ delete 11
    $ delete 8
    $ rs

  export
  solve : (RuleSet, List Message) -> Maybe Nat
  solve (rs', messages) = do
    let rs = prepareRuleSet rs'
    let ruleTree = calculateRuleTree rs 0
    let codeMatcher = buildCodeMatcher changeRule0 ruleTree
    map (count id) $ traverse (matchCode codeMatcher) messages

testInput : String
testInput =
"0: 4 1 5\
1: 2 3 | 3 2\
2: 4 4 | 5 5\
3: 4 5 | 5 4\
4: \"a\"\
5: \"b\"\
6: 2 3\
\
ababbb\
bababa\
abbbab\
aaabbb\
aaaabbb
"

testInput2 : String
testInput2 =
"42: 9 14 | 10 1\
9: 14 27 | 1 26\
10: 23 14 | 28 1\
1: \"a\"\
11: 42 31\
5: 1 14 | 15 1\
19: 14 1 | 14 14\
12: 24 14 | 19 1\
16: 15 1 | 14 14\
31: 14 17 | 1 13\
6: 14 14 | 1 14\
2: 1 24 | 14 4\
0: 8 11\
13: 14 3 | 1 12\
15: 1 | 14\
17: 14 2 | 1 7\
23: 25 1 | 22 14\
28: 16 1\
4: 1 1\
20: 14 14 | 1 15\
3: 5 14 | 16 1\
27: 1 6 | 14 18\
14: \"b\"\
21: 14 1 | 1 14\
25: 1 1 | 1 14\
22: 14 14\
8: 42\
26: 14 22 | 1 20\
18: 15 15\
7: 14 5 | 1 21\
24: 14 1\
\
abbbbbabbbaaaababbaabbbbabababbbabbbbbbabaaaa\
bbabbbbaabaabba\
babbbbaabbbbbabbbbbbaabaaabaaa\
aaabbbbbbaaaabaababaabababbabaaabbababababaaa\
bbbbbbbaaaabbbbaaabbabaaa\
bbbababbbbaaaaaaaabbababaaababaabab\
ababaaaaaabaaab\
ababaaaaabbbaba\
baabbaaaabbaaaababbaababb\
abbbbabbbbaaaababbbbbbaaaababb\
aaaaabbaabaaaaababaa\
aaaabbaaaabbaaa\
aaaabbaabbaaaaaaabbbabbbaaabbaabaaa\
babaaabbbaaabaababbaabababaaab\
aabbbbbaabbbaaaaaabbbbbababaaaaabbaaabba
"

main : IO ()
main = do
  Right content <- readFile "day19i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  -- let Just (rs, msgs) = parseInput testInput2
  let Just (rs, msgs) = parseInput content
      | Nothing => putStrLn "Parse error."
  putStrLn "First part."
  printLn $ FirstPart.solve (rs, msgs)
  putStrLn "Second part."
  printLn $ SecondPart.solve (rs, msgs)
