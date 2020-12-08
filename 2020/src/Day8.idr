module Day8

{-
--- Day 8: Handheld Halting ---
Your flight to the major airline hub reaches cruising altitude without incident. While you consider checking the in-flight menu for one of those drinks that come with a little umbrella, you are interrupted by the kid sitting next to you.

Their handheld game console won't turn on! They ask if you can take a look.

You narrow the problem down to a strange infinite loop in the boot code (your puzzle input) of the device. You should be able to fix it, but first you need to be able to run the code in isolation.

The boot code is represented as a text file with one instruction per line of text. Each instruction consists of an operation (acc, jmp, or nop) and an argument (a signed number like +4 or -20).

acc increases or decreases a single global value called the accumulator by the value given in the argument. For example, acc +7 would increase the accumulator by 7. The accumulator starts at 0. After an acc instruction, the instruction immediately below it is executed next.
jmp jumps to a new instruction relative to itself. The next instruction to execute is found using the argument as an offset from the jmp instruction; for example, jmp +2 would skip the next instruction, jmp +1 would continue to the instruction immediately below it, and jmp -20 would cause the instruction 20 lines above to be executed next.
nop stands for No OPeration - it does nothing. The instruction immediately below it is executed next.
For example, consider the following program:

nop +0
acc +1
jmp +4
acc +3
jmp -3
acc -99
acc +1
jmp -4
acc +6
These instructions are visited in this order:

nop +0  | 1
acc +1  | 2, 8(!)
jmp +4  | 3
acc +3  | 6
jmp -3  | 7
acc -99 |
acc +1  | 4
jmp -4  | 5
acc +6  |
First, the nop +0 does nothing. Then, the accumulator is increased from 0 to 1 (acc +1) and jmp +4 sets the next instruction to the other acc +1 near the bottom. After it increases the accumulator from 1 to 2, jmp -4 executes, setting the next instruction to the only acc +3. It sets the accumulator to 5, and jmp -3 causes the program to continue back at the first acc +1.

This is an infinite loop: with this sequence of jumps, the program will run forever. The moment the program tries to run any instruction a second time, you know it will never terminate.

Immediately before the program would run an instruction a second time, the value in the accumulator is 5.

Run your copy of the boot code. Immediately before any instruction is executed a second time, what value is in the accumulator?

Your puzzle answer was 1801.

--- Part Two ---
After some careful analysis, you believe that exactly one instruction is corrupted.

Somewhere in the program, either a jmp is supposed to be a nop, or a nop is supposed to be a jmp. (No acc instructions were harmed in the corruption of this boot code.)

The program is supposed to terminate by attempting to execute an instruction immediately after the last instruction in the file. By changing exactly one jmp or nop, you can repair the boot code and make it terminate correctly.

For example, consider the same program from above:

nop +0
acc +1
jmp +4
acc +3
jmp -3
acc -99
acc +1
jmp -4
acc +6
If you change the first instruction from nop +0 to jmp +0, it would create a single-instruction infinite loop, never leaving that instruction. If you change almost any of the jmp instructions, the program will still eventually find another jmp instruction and loop forever.

However, if you change the second-to-last instruction (from jmp -4 to nop -4), the program terminates! The instructions are visited in this order:

nop +0  | 1
acc +1  | 2
jmp +4  | 3
acc +3  |
jmp -3  |
acc -99 |
acc +1  | 4
nop -4  | 5
acc +6  | 6
After the last instruction (acc +6), the program terminates by attempting to run the instruction below the last instruction in the file. With this change, after the program terminates, the accumulator contains the value 8 (acc +1, acc +1, acc +6).

Fix the program so that it terminates normally by changing exactly one jmp (to nop) or nop (to jmp). What is the value of the accumulator after the program terminates?

Your puzzle answer was 2060.
-}

import System.File
import Data.Strings
import Data.List

%default total

data Instruction : Type where
  Nop : Int -> Instruction
  Acc : Int -> Instruction
  Jmp : Int -> Instruction

Show Instruction where
  show (Nop p) = "nop " ++ show p
  show (Acc p) = "acc " ++ show p
  show (Jmp p) = "jmp " ++ show p

Program : Type
Program = List Instruction

namespace Parser

  parseLine : String -> Maybe Instruction
  parseLine str = case words str of
    ["nop", param] => map Nop $ parseInteger param
    ["acc", param] => map Acc $ parseInteger param
    ["jmp", param] => map Jmp $ parseInteger param
    _              => Nothing

  export
  parseProgram : String -> Program
  parseProgram = mapMaybe parseLine . lines

testInput : String
testInput =
"nop +0\
acc +1\
jmp +4\
acc +3\
jmp -3\
acc -99\
acc +1\
jmp -4\
acc +6\
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

-- ### Use of auto parameters: This makes nice smart constructors.
fromListCrt : (l : List a) -> {auto 0 ok : NonEmpty l} -> ZipList a
fromListCrt [] impossible
fromListCrt (x :: xs) = ZL [] x xs

toList : ZipList a -> List a
toList (ZL rs x ls) = reverse rs ++ (x :: ls)

stepRight : ZipList a -> Maybe (ZipList a)
stepRight (ZL _ _ []) = Nothing
stepRight (ZL ls l (r :: rs)) = Just (ZL (l::ls) r rs)

stepLeft : ZipList a -> Maybe (ZipList a)
stepLeft (ZL [] _ _) = Nothing
stepLeft (ZL (l :: ls) r rs) = Just (ZL ls l (r :: rs))

namespace Machine

  -- ### Public visibility from namespaces
  public export
  Acc : Type
  Acc = Int

  -- Instruction counter
  IC : Type
  IC = Nat

  Computer : Type
  Computer = ZipList (Instruction, Maybe IC)

  public export
  data Result
    = Aborted (Acc, IC)
    | Completed Acc

  export
  Show Result where
    show (Aborted a)   = "Aborted " ++ show a
    show (Completed c) = "Completed " ++ show c

  updateIC : IC -> Computer -> Computer
  updateIC ic (ZL ls (i,_) rs) = ZL ls (i,Just ic) rs

  partial
  jmp : Int -> Computer -> Maybe Computer
  jmp 0 c = Just c
  jmp n c = if n < 0
    then do
      c' <- stepLeft c
      jmp (n + 1) c'
    else do
      c' <- stepRight c
      jmp (n - 1) c'

  partial
  run : Acc -> IC -> Computer -> IO Result
  run acc ic machine = do
    let (instr, Nothing) = machine.focus
          | (_, Just _) => pure $ Aborted (acc, ic)
    let (newAcc, newMachine) = the (Acc, Maybe Computer) $ case instr of
          Nop _ => (acc    , stepRight $ updateIC ic machine)
          Acc a => (acc + a, stepRight $ updateIC ic machine)
          Jmp j => (acc    , jmp j     $ updateIC ic machine)
    case newMachine of
      Nothing => pure $ Completed newAcc
      Just m' => run newAcc (ic + 1) m'

  export
  partial
  execute : (p : Program) -> {auto 0 ok : NonEmpty p} -> IO Result
  execute (i :: is) = run 0 0 $ fromListCrt $ (map (\i => (i, Nothing)) (i :: is))

namespace SecondPart

  swapOp : ZipList Instruction -> ZipList Instruction
  swapOp (ZL ls (Nop i) rs) = ZL ls (Jmp i) rs
  swapOp (ZL ls (Jmp i) rs) = ZL ls (Nop i) rs
  swapOp zl                 = zl

  partial
  search : ZipList Instruction -> IO (Maybe Acc)
  search zl = do
    let modProg = toList $ swapOp zl
    let Yes _ = nonEmpty modProg
         | No _ => pure Nothing
    res <- execute modProg
    case res of
      Completed a => pure $ Just a
      _ => do
        let Just zl' = stepRight zl
            | Nothing => pure Nothing
        search zl'

  export
  partial
  findWorkingProgram : (p : Program) -> {auto 0 ok : NonEmpty p} -> IO (Maybe Acc)
  findWorkingProgram p = search $ fromListCrt p

partial
main : IO ()
main = do
  Right content <- readFile "day8i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let program = parseProgram content
  -- let program = parseProgram testInput
  let Yes _ = nonEmpty program
      | No _ => printLn "Got empty program."
  putStrLn "First part."
  execute program >>= printLn
  putStrLn "Second part."
  findWorkingProgram program >>= printLn
