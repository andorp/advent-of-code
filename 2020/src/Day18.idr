module Day18

{-
--- Day 18: Operation Order ---
As you look out the window and notice a heavily-forested continent slowly appear over the horizon, you are interrupted by the child sitting next to you. They're curious if you could help them with their math homework.

Unfortunately, it seems like this "math" follows different rules than you remember.

The homework (your puzzle input) consists of a series of expressions that consist of addition (+), multiplication (*), and parentheses ((...)). Just like normal math, parentheses indicate that the expression inside must be evaluated before it can be used by the surrounding expression. Addition still finds the sum of the numbers on both sides of the operator, and multiplication still finds the product.

However, the rules of operator precedence have changed. Rather than evaluating multiplication before addition, the operators have the same precedence, and are evaluated left-to-right regardless of the order in which they appear.

For example, the steps to evaluate the expression 1 + 2 * 3 + 4 * 5 + 6 are as follows:

1 + 2 * 3 + 4 * 5 + 6
  3   * 3 + 4 * 5 + 6
      9   + 4 * 5 + 6
         13   * 5 + 6
             65   + 6
                 71
Parentheses can override this order; for example, here is what happens if parentheses are added to form 1 + (2 * 3) + (4 * (5 + 6)):

1 + (2 * 3) + (4 * (5 + 6))
1 +    6    + (4 * (5 + 6))
     7      + (4 * (5 + 6))
     7      + (4 *   11   )
     7      +     44
            51
Here are a few more examples:

2 * 3 + (4 * 5) becomes 26.
5 + (8 * 3 + 9 + 3 * 4 * 3) becomes 437.
5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4)) becomes 12240.
((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2 becomes 13632.
Before you can help with the homework, you need to understand it yourself. Evaluate the expression on each line of the homework; what is the sum of the resulting values?

Your puzzle answer was 23507031841020.

--- Part Two ---
You manage to answer the child's questions and they finish part 1 of their homework, but get stuck when they reach the next section: advanced math.

Now, addition and multiplication have different precedence levels, but they're not the ones you're familiar with. Instead, addition is evaluated before multiplication.

For example, the steps to evaluate the expression 1 + 2 * 3 + 4 * 5 + 6 are now as follows:

1 + 2 * 3 + 4 * 5 + 6
  3   * 3 + 4 * 5 + 6
  3   *   7   * 5 + 6
  3   *   7   *  11
     21       *  11
         231
Here are the other examples from above:

1 + (2 * 3) + (4 * (5 + 6)) still becomes 51.
2 * 3 + (4 * 5) becomes 46.
5 + (8 * 3 + 9 + 3 * 4 * 3) becomes 1445.
5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4)) becomes 669060.
((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2 becomes 23340.
What do you get if you add up the results of evaluating the homework problems using these new rules?

Your puzzle answer was 218621700997826.
-}

import System.File
import Text.Lexer
import Text.Parser
import Data.List
import Debug.Trace

traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

namespace Machine

  public export
  data Op = Mult | Plus

  Eq Op where
    Mult == Mult = True
    Plus == Plus = True
    _ == _ = False

  public export
  data Operation
    = Push Integer
    | Cmd  Op
    | NewFrame
    | EndFrame

  export
  Eq Operation where
    (Push x) == (Push y)  = x == y
    (Cmd  x) == (Cmd  y)  = x == y
    NewFrame == NewFrame  = True
    EndFrame == EndFrame  = True
    _ == _ = False

  Program : Type
  Program = List Operation

  export
  record Machine where
    constructor MkMachine
    stack : List (Integer, Op)
    acc : Integer
    op  : Op

  initMachine : Machine
  initMachine = MkMachine [] 0 Plus

  result : Machine -> Integer
  result (MkMachine _ a _) = a

  command : Op -> Integer -> Integer -> Integer
  command Mult a b = a * b
  command Plus a b = a + b

  push : Integer -> Machine -> Machine
  push n (MkMachine stack acc op) = MkMachine stack (command op acc n) op

  setOp : Op -> Machine -> Machine
  setOp o (MkMachine stack acc _) = MkMachine stack acc o

  newFrame : Machine -> Machine
  newFrame (MkMachine stack acc op) = MkMachine ((acc,op) :: stack) 0 Plus

  endFrame : Machine -> Machine
  endFrame (MkMachine [] acc op) = trace "Empty stack" (MkMachine [] acc op)
  endFrame (MkMachine ((acc0,op0) :: stack) acc1 op1) = MkMachine stack (command op0 acc0 acc1) op0

  export
  runMachine : List Operation -> Integer
  runMachine = result . foldl runOp initMachine
    where
      runOp : Machine -> Operation -> Machine
      runOp m o = case o of
        Push x   => push x m
        Cmd  x   => setOp x m
        NewFrame => newFrame m
        EndFrame => endFrame m

namespace Expr

  public export
  data Expr : Type where
    Val : Integer -> Expr
    Add : Expr -> Expr -> Expr
    Mul : Expr -> Expr -> Expr

  export
  eval : Expr -> Integer
  eval (Val x) = x
  eval (Add e1 e2) = eval e1 + eval e2
  eval (Mul e1 e2) = eval e1 * eval e2

namespace Parser

  data ExprTokenK
    = OpenParen
    | CloseParen
    | OpPlus
    | OpMult
    | Number
    | Newline
    | Space

  Eq ExprTokenK where
    OpenParen   == OpenParen  = True
    CloseParen  == CloseParen = True
    OpPlus      == OpPlus     = True
    OpMult      == OpMult     = True
    Number      == Number     = True
    Newline     == Newline    = True
    Space       == Space      = True
    _ == _ = False

  TokenKind ExprTokenK where
    TokType OpenParen   = ()
    TokType CloseParen  = ()
    TokType OpPlus      = Op
    TokType OpMult      = Op
    TokType Number      = Integer
    TokType Newline     = ()
    TokType Space       = ()

    tokValue OpenParen  _ = ()
    tokValue CloseParen _ = ()
    tokValue OpPlus     _ = Plus
    tokValue OpMult     _ = Mult
    tokValue Number     d = cast d
    tokValue Newline    _ = ()
    tokValue Space      _ = ()

  ExprToken : Type
  ExprToken = Token ExprTokenK

  exprTokenMap : TokenMap ExprToken
  exprTokenMap = toTokenMap
    [ (newline, Newline)
    , (is '(', OpenParen)
    , (is ')', CloseParen)
    , (is '+', OpPlus)
    , (is '*', OpMult)
    , (some digits, Number)
    , (spaces, Space)
    ]

  export
  lexExprs : String -> Maybe (List ExprToken)
  lexExprs str = case lex exprTokenMap str of
    (tokens,_,_, "")  => Just $ filter (\(Tok t _) => t /= Space) $ map TokenData.tok tokens
    _                 => Nothing

  operation : Grammar ExprToken True Operation
  operation = choice
    [ map (const NewFrame) $ match OpenParen
    , map (const EndFrame) $ match CloseParen
    , Cmd  <$> match OpPlus
    , Cmd  <$> match OpMult
    , Push <$> match Number
    ]

  program : Grammar ExprToken True Program
  program = someTill (match Newline) operation

  parsePrograms : List ExprToken -> Maybe (List Program)
  parsePrograms toks = case parse (some program) toks of
    Right (d, ts) => Just d
    _             => Nothing

  export
  parseMachineInput : String -> Maybe (List Program)
  parseMachineInput str = do
    tokens <- lexExprs str
    parsePrograms $ tokens

  mutual
    exprM : Grammar ExprToken True Expr
    exprM = map (\(xs ** _) => foldr1 Mul xs) $ sepBy1' (match OpMult) exprA

    exprA : Grammar ExprToken True Expr
    exprA = map (\(xs ** _) => foldr1 Add xs) $ sepBy1' (match OpPlus) exprV

    exprV : Grammar ExprToken True Expr
    exprV = (Val <$> match Number)
        <|> between (match OpenParen) (match CloseParen) exprM

  parseExprs : List ExprToken -> Maybe (List Expr)
  parseExprs toks = case parse (endBy1 (match Newline) exprM) toks of
    Right (d, ts) => Just d
    _             => Nothing

  export
  parseExprInput : String -> Maybe (List Expr)
  parseExprInput str = do
    tokens <- lexExprs str
    parseExprs tokens

namespace FirstPart

  export
  solve : String -> Maybe Integer
  solve cnt = do
    ps <- parseMachineInput cnt
    Just $ sum' $ map runMachine ps

namespace SecondPart

  export
  solve : String -> Maybe Integer
  solve cnt = do
    es <- parseExprInput cnt
    Just $ sum' $ map eval es

testInput : String
testInput =
"1 + 2 * 3 + 4 * 5 + 6\
1 + (2 * 3) + (4 * (5 + 6))\
2 * 3 + (4 * 5)\
5 + (8 * 3 + 9 + 3 * 4 * 3)\
5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))\
((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2\
"

main : IO ()
main = do
  Right content <- readFile "day18i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  putStrLn "First part."
  printLn $ FirstPart.solve content
  putStrLn "Second part."
  printLn $ SecondPart.solve content
