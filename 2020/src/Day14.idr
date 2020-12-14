module Day14

{-
--- Day 14: Docking Data ---
As your ferry approaches the sea port, the captain asks for your help again. The computer system that runs this port isn't compatible with the docking program on the ferry, so the docking parameters aren't being correctly initialized in the docking program's memory.

After a brief inspection, you discover that the sea port's computer system uses a strange bitmask system in its initialization program. Although you don't have the correct decoder chip handy, you can emulate it in software!

The initialization program (your puzzle input) can either update the bitmask or write a value to memory. Values and memory addresses are both 36-bit unsigned integers. For example, ignoring bitmasks for a moment, a line like mem[8] = 11 would write the value 11 to memory address 8.

The bitmask is always given as a string of 36 bits, written with the most significant bit (representing 2^35) on the left and the least significant bit (2^0, that is, the 1s bit) on the right. The current bitmask is applied to values immediately before they are written to memory: a 0 or 1 overwrites the corresponding bit in the value, while an X leaves the bit in the value unchanged.

For example, consider the following program:

mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
mem[8] = 11
mem[7] = 101
mem[8] = 0
This program starts by specifying a bitmask (mask = ....). The mask it specifies will overwrite two bits in every written value: the 2s bit is overwritten with 0, and the 64s bit is overwritten with 1.

The program then attempts to write the value 11 to memory address 8. By expanding everything out to individual bits, the mask is applied as follows:

value:  000000000000000000000000000000001011  (decimal 11)
mask:   XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
result: 000000000000000000000000000001001001  (decimal 73)
So, because of the mask, the value 73 is written to memory address 8 instead. Then, the program tries to write 101 to address 7:

value:  000000000000000000000000000001100101  (decimal 101)
mask:   XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
result: 000000000000000000000000000001100101  (decimal 101)
This time, the mask has no effect, as the bits it overwrote were already the values the mask tried to set. Finally, the program tries to write 0 to address 8:

value:  000000000000000000000000000000000000  (decimal 0)
mask:   XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
result: 000000000000000000000000000001000000  (decimal 64)
64 is written to address 8 instead, overwriting the value that was there previously.

To initialize your ferry's docking program, you need the sum of all values left in memory after the initialization program completes. (The entire 36-bit address space begins initialized to the value 0 at every address.) In the above example, only two values in memory are not zero - 101 (at address 7) and 64 (at address 8) - producing a sum of 165.

Execute the initialization program. What is the sum of all values left in memory after it completes?

Your puzzle answer was 13865835758282.

--- Part Two ---
For some reason, the sea port's computer system still can't communicate with your ferry's docking program. It must be using version 2 of the decoder chip!

A version 2 decoder chip doesn't modify the values being written at all. Instead, it acts as a memory address decoder. Immediately before a value is written to memory, each bit in the bitmask modifies the corresponding bit of the destination memory address in the following way:

If the bitmask bit is 0, the corresponding memory address bit is unchanged.
If the bitmask bit is 1, the corresponding memory address bit is overwritten with 1.
If the bitmask bit is X, the corresponding memory address bit is floating.
A floating bit is not connected to anything and instead fluctuates unpredictably. In practice, this means the floating bits will take on all possible values, potentially causing many memory addresses to be written all at once!

For example, consider the following program:

mask = 000000000000000000000000000000X1001X
mem[42] = 100
mask = 00000000000000000000000000000000X0XX
mem[26] = 1
When this program goes to write to memory address 42, it first applies the bitmask:

address: 000000000000000000000000000000101010  (decimal 42)
mask:    000000000000000000000000000000X1001X
result:  000000000000000000000000000000X1101X
After applying the mask, four bits are overwritten, three of which are different, and two of which are floating. Floating bits take on every possible combination of values; with two floating bits, four actual memory addresses are written:

000000000000000000000000000000011010  (decimal 26)
000000000000000000000000000000011011  (decimal 27)
000000000000000000000000000000111010  (decimal 58)
000000000000000000000000000000111011  (decimal 59)
Next, the program is about to write to memory address 26 with a different bitmask:

address: 000000000000000000000000000000011010  (decimal 26)
mask:    00000000000000000000000000000000X0XX
result:  00000000000000000000000000000001X0XX
This results in an address with three floating bits, causing writes to eight memory addresses:

000000000000000000000000000000010000  (decimal 16)
000000000000000000000000000000010001  (decimal 17)
000000000000000000000000000000010010  (decimal 18)
000000000000000000000000000000010011  (decimal 19)
000000000000000000000000000000011000  (decimal 24)
000000000000000000000000000000011001  (decimal 25)
000000000000000000000000000000011010  (decimal 26)
000000000000000000000000000000011011  (decimal 27)
The entire 36-bit address space still begins initialized to the value 0 at every address, and you still need the sum of all values left in memory at the end of the program. In this example, the sum is 208.

Execute the initialization program using an emulator for a version 2 decoder chip. What is the sum of all values left in memory after it completes?

Your puzzle answer was 4195339838136.
-}

import System.File
import Data.SortedMap
import Data.IORef
import Data.Strings
import Data.Vect
import Debug.Trace
import Data.List

%default total

traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

-- ### Primitive operations in Idris
band : Bits64 -> Bits64 -> Bits64
band = prim__and_Bits64

bor : Bits64 -> Bits64 -> Bits64
bor = prim__or_Bits64

bshiftr : Bits64 -> Bits64
bshiftr b = prim__shr_Bits64 b 1

Mask : Type
Mask = Vect 36 Char

-- ### Primitive types in Idris
Addr : Type
Addr = Bits64

-- ### Interesting type class instances.
FromString (Maybe Mask) where
  fromString str = toVect 36 $ unpack str

namespace Machine

  -- ### Free-monad like DSL pattern
  public export
  data Ins : Type -> Type where
    Pure    : a -> Ins a
    (>>=)   : Ins a -> (a -> Ins b) -> Ins b
    SetMask : Mask -> Ins ()
    Mem     : Bits64 -> Bits64 -> Ins ()

  export
  sequence : List (Ins ()) -> Ins ()
  sequence []        = Pure ()
  sequence (i :: is) = i >>= const (sequence is)

  export
  Show (Ins a) where
    show (Pure _)     = "pure ?"
    show (_ >>= _)    = "? >>= ?"
    show (SetMask m)  = "SetMask " ++ show m
    show (Mem a c)    = "Mem " ++ show a ++ " " ++ show c

  -- ### Do notation desugars to pure and >>=
  pure : a -> Ins a
  pure = Pure

  public export
  record Interp s where
    constructor MkInterp
    init    : s
    setMask : Mask -> s -> s
    setMem  : Addr -> Bits64 -> s -> s

  partial
  run : IORef s -> Interp s -> Ins a -> IO a
  run ref _ (Pure a)        = pure a
  run ref i (a >>= k)       = (run ref i a) >>= {- of IO -} (run ref i . k)
  run ref i (SetMask m)     = modifyIORef ref (setMask i m)
  run ref i (Mem addr cnt)  = modifyIORef ref (setMem i addr cnt)

  export
  partial
  runMachine : Interp s -> Ins () -> IO s
  runMachine interp ins = do
    ref <- newIORef (init interp)
    run ref interp ins
    readIORef ref

namespace Parser

  parseLine : String -> Maybe (Ins ())
  parseLine str = case Strings.words str of
    ["mask","=",mask]
      => map SetMask $ fromString mask
    [mem, "=", val]
      => case unpack mem of
          ('m' :: 'e' :: 'm' :: '[' :: addr) => do
            addr' <- map pack $ init' addr
            Mem <$> parsePositive addr' <*> parsePositive val
          other
            => trace ("Parser found invalid line: " ++ show other) Nothing
    other => trace ("Parser found invalid line: " ++ show other) Nothing

  export
  parseProgram : String -> List (Ins ())
  parseProgram str = mapMaybe parseLine $ lines str

namespace FirstPart

  record State where
    constructor MkState
    mask : (Bits64, Bits64)
    memory : SortedMap Addr Bits64

  init : State
  init = MkState (0,0) empty -- The first instruction is expected to be a MASK.

  calcMask : Vect 36 Char -> (Bits64, Bits64)
  calcMask xs = foldl
    (\(am, om) , c => case c of
      '0' => (2 * am, 2 * om + 0)
      '1' => (2 * am, 2 * om + 1)
      _   => (2 * am + 1, 2 * om))
    (0,0)
    xs

  applyMask : (Bits64, Bits64) -> Bits64 -> Bits64
  applyMask (a,o) c = (bor o (band c a))

  setMask : Mask -> State -> State
  setMask m s = record { mask = calcMask m } s

  setMem : Addr -> Bits64 -> State -> State
  setMem a c s = record { memory $= insert a (applyMask s.mask c) } s

  interpreter : Interp State
  interpreter = MkInterp init setMask setMem

  export
  partial
  solve : Ins () -> IO Integer
  solve ins = do
    st <- runMachine interpreter ins
    pure $ foldl (\a , b => a + cast b) 0 st.memory


namespace SecondPart

  AddrPattern : Type
  AddrPattern = Mask

  record State2 where
    constructor MkState2
    mask : Mask
    memory : SortedMap Bits64 Bits64

  init : State2
  init = MkState2 (replicate 36 '0') empty -- The first instruction is expected to be a MASK

  addressToMask : Bits64 -> Mask
  addressToMask addr = reverse $ go 36 addr
    where
      go : (n : Nat) -> Bits64 -> Vect n Char
      go Z     _ = []
      go (S n) a = case (band a 1) of
        0 => '0' :: go n (bshiftr a)
        1 => '1' :: go n (bshiftr a)
        _ => trace "addressToMask" '?' :: go n (bshiftr a)

  addressPattern : Mask -> Mask -> AddrPattern
  addressPattern addr mask =
    zipWith
      (\a , m => case (a,m) of
        (c, '0') => c
        (_, '1') => '1'
        (_, 'X') => 'X'
        _        => trace "addressPattern" '?')
      addr
      mask

  buildAddresses : AddrPattern -> List Addr
  buildAddresses = foldl
    (\addrs , m => case m of
      '0' => map (\a => 2 * a + 0) addrs
      '1' => map (\a => 2 * a + 1) addrs
      'X' => concatMap (\a => [2 * a + 0, 2 * a + 1]) addrs
      _   => trace "buildAddresses" (map (2*) addrs))
    [0] -- when building more than zero addresses, there will be at least one addr, thus [0] works here

  setMask : Mask -> State2 -> State2
  setMask m = record { mask = m }

  setMem : Addr -> Bits64 -> State2 -> State2
  setMem a c s =
    let addrPtn = addressPattern (addressToMask a) s.mask
        memory' = foldl (\m , a' => insert a' c m) s.memory $ buildAddresses addrPtn
    in record { memory = memory' } s

  interpreter : Interp State2
  interpreter = MkInterp init setMask setMem

  export
  partial
  solve : Ins () -> IO Integer
  solve ins = do
    st <- runMachine interpreter ins
    pure $ foldl (\a , b => a + cast b) 0 (State2.memory st)

testProgram : Ins ()
testProgram = do
  let Just m = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X"
      | Nothing => pure ()
  SetMask m
  Mem 8 11
  Mem 7 101
  Mem 8 0

testInput : String
testInput =
"mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X\
mem[8] = 11\
mem[7] = 101\
mem[8] = 0
"

testInput2 : String
testInput2 =
"mask = 000000000000000000000000000000X1001X\
mem[42] = 100\
mask = 00000000000000000000000000000000X0XX\
mem[26] = 1
"

partial
main : IO ()
main = do
  Right content <- readFile "day14i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
  let program = parseProgram content
  -- let program = parseProgram testInput
  putStrLn "First Part."
  FirstPart.solve (sequence program) >>= printLn
  -- let program = parseProgram testInput2
  putStrLn "Second Part."
  SecondPart.solve (sequence program) >>= printLn
  pure ()
