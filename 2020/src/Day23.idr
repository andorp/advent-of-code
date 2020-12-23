module Day23

{-
--- Day 23: Crab Cups ---
The small crab challenges you to a game! The crab is going to mix up some cups, and you have to predict where they'll end up.

The cups will be arranged in a circle and labeled clockwise (your puzzle input). For example, if your labeling were 32415, there would be five cups in the circle; going clockwise around the circle from the first cup, the cups would be labeled 3, 2, 4, 1, 5, and then back to 3 again.

Before the crab starts, it will designate the first cup in your list as the current cup. The crab is then going to do 100 moves.

Each move, the crab does the following actions:

The crab picks up the three cups that are immediately clockwise of the current cup. They are removed from the circle; cup spacing is adjusted as necessary to maintain the circle.
The crab selects a destination cup: the cup with a label equal to the current cup's label minus one. If this would select one of the cups that was just picked up, the crab will keep subtracting one until it finds a cup that wasn't just picked up. If at any point in this process the value goes below the lowest value on any cup's label, it wraps around to the highest value on any cup's label instead.
The crab places the cups it just picked up so that they are immediately clockwise of the destination cup. They keep the same order as when they were picked up.
The crab selects a new current cup: the cup which is immediately clockwise of the current cup.
For example, suppose your cup labeling were 389125467. If the crab were to do merely 10 moves, the following changes would occur:

In the above example, the cups' values are the labels as they appear moving clockwise around the circle; the current cup is marked with ( ).

After the crab is done, what order will the cups be in? Starting after the cup labeled 1, collect the other cups' labels clockwise into a single string with no extra characters; each number except 1 should appear exactly once. In the above example, after 10 moves, the cups clockwise from 1 are labeled 9, 2, 6, 5, and so on, producing 92658374. If the crab were to complete all 100 moves, the order after cup 1 would be 67384529.

Using your labeling, simulate 100 moves. What are the labels on the cups after cup 1?

Your puzzle answer was 25398647.

--- Part Two ---
Due to what you can only assume is a mistranslation (you're not exactly fluent in Crab), you are quite surprised when the crab starts arranging many cups in a circle on your raft - one million (1000000) in total.

Your labeling is still correct for the first few cups; after that, the remaining cups are just numbered in an increasing fashion starting from the number after the highest number in your list and proceeding one by one until one million is reached. (For example, if your labeling were 54321, the cups would be numbered 5, 4, 3, 2, 1, and then start counting up from 6 until one million is reached.) In this way, every number from one through one million is used exactly once.

After discovering where you made the mistake in translating Crab Numbers, you realize the small crab isn't going to do merely 100 moves; the crab is going to do ten million (10000000) moves!

The crab is going to hide your stars - one each - under the two cups that will end up immediately clockwise of cup 1. You can have them if you predict what the labels on those cups will be when the crab is finished.

In the above example (389125467), this would be 934001 and then 159792; multiplying these together produces 149245887792.

Determine which two cups will end up immediately clockwise of cup 1. What do you get if you multiply their labels together?

Your puzzle answer was 363807398885.

Both parts of this puzzle are complete! They provide two gold stars: **

At this point, you should return to your Advent calendar and try another puzzle.

Your puzzle input was 952316487.

You can also [Share] this puzzle.
-}

import Data.Stream
import Data.Vect
import Data.List
import Data.Strings
import Debug.Trace
import Data.IOArray

%default total

traceIt : Show a => a -> a
traceIt x = trace (show x) x

Cups : Type
Cups = Vect 9 Nat

testInput : Cups
testInput = [3,8,9,1,2,5,4,6,7]

namespace FirstPart

  LIMIT : Nat
  LIMIT = 9

  pred : Nat -> Nat
  pred Z = LIMIT
  pred (S Z) = LIMIT
  pred (S n) = n

  partial
  findNext : Nat -> Vect 3 Nat -> Nat
  findNext n ps =
    let p = pred n
    in if elem p ps then findNext p ps else p

  record Game where
    constructor MkGame
    focus   : Nat
    pickups : Vect 3 Nat
    rest    : Vect 5 Nat

  Show Game where
    show (MkGame f ps rs) = unwords [show f, show ps, show rs]

  nextFocus : Game -> Nat
  nextFocus (MkGame _ _ (n :: _)) = n

  rotate : Game -> Game
  rotate (MkGame h ps (r::rs)) = MkGame r ps (rs ++ [h])

  -- TODO: There should be a proof that next is in the game!
  partial
  rotateTillNext : Nat -> Game -> Game
  rotateTillNext next g = if focus g == next then g else rotateTillNext next (rotate g)

  partial
  rotateCups : Nat -> Cups -> Cups
  rotateCups n (x :: xs) = if x == n then (x :: xs) else rotateCups n (xs ++ [x])

  fromCups : Cups -> Game
  fromCups [f,p1,p2,p3,r1,r2,r3,r4,r5] = MkGame f [p1,p2,p3] [r1,r2,r3,r4,r5]

  toCups : Game -> Cups
  toCups g = (focus g) :: pickups g ++ rest g

  partial
  round : Cups -> Cups
  round c =
    let g = fromCups c
        n = nextFocus g
    in rotateCups n $ toCups $ rotateTillNext (findNext (focus g) (pickups g)) g

  export
  partial
  solve : Cups -> Vect 9 Nat
  solve input = rotateCups 1 $ index 100 $ iterate round input

namespace SecondPart

  Idx : Type
  Idx = Int

  -- Note indexes are shifted by one
  data Gamee : Int -> Type where
    MkGamee : (pointer : IOArray Idx) -> (focus : Idx) -> Gamee n

  setFocus : Idx -> Gamee n -> Gamee n
  setFocus f (MkGamee arr _) = MkGamee arr f

  partial
  createGame : List Int -> (n : Int) -> IO (Gamee n)
  createGame xs n = do
    putStrLn "createGame.started"
    arr <- newArray n
    putStrLn "createGame.add"
    let ys = map (\x => x - 1) xs
    let (f :: s :: _) = ys
    writeArray arr f s
    putStrLn "createGame.copyList"
    lst <- copyList 0 f ys arr
    putStrLn "createGame.copyList.done"
    writeArray arr lst f
    pure (MkGamee arr f)
    where
      copyList : Int -> Idx -> List Idx -> IOArray Int -> IO Idx
      copyList n l [] arr
        = if n >= max arr
            then pure l
            else do
              if (mod n 1000 == 0) then printLn n else pure ()
              writeArray arr l n
              copyList (n + 1) n [] arr
      copyList n l (i :: is) arr = do
        writeArray arr l i
        copyList (n + 1) i is arr

  fromList : (xs : List Int) -> IO (Gamee (cast (List.length xs)))
  fromList xs = do
    arr <- IOArray.fromList $ map Just xs
    pure $ MkGamee arr 0

  partial
  elemLinkedList : Gamee n -> Idx -> IO (List Idx)
  elemLinkedList g@(MkGamee arr f) e =
    if e == f
      then pure []
      else do
        Just n <- readArray arr e
          | _ => do putStrLn $ "elemLinkedList: " ++ show e
                    pure []
        map (e + 1 ::) $ elemLinkedList g n

  partial
  -- ### forall n . is {n} ->
  showGamee : forall n . Gamee n -> IO String
  showGamee {n} g@(MkGamee arr f) = do
    xs <- IOArray.toList arr
    Just n <- readArray arr f
    elems <- elemLinkedList g n
    pure $ show (f+1, elems)
    where

  partial
  renderResult : forall n . Gamee n -> IO String
  renderResult g@(MkGamee arr _) = do
    Just s1 <- readArray arr 0
    Just s2 <- readArray arr s1
    printLn (s1 + 1, s2 + 1)
    pure $ show $ (s1 + 1) * (s2 + 1)

  partial
  pickupsAndRest : Gamee n -> IO (Vect 3 Idx, Idx)
  pickupsAndRest (MkGamee arr f) = do
    Just p1 <- readArray arr f
    Just p2 <- readArray arr p1
    Just p3 <- readArray arr p2
    Just rest <- readArray arr p3
    pure ([p1,p2,p3], rest)

  pred : Int -> Idx -> Idx
  pred n m = if (m <= 0) then (n - 1) else (m - 1)

  partial
  calcDest : Int -> Idx -> Vect 3 Idx -> Idx
  calcDest m i ps =
    let p = pred m i
    in if elem p ps then calcDest m p ps else p

  partial
  round : {n : Int} -> Gamee n -> IO (Gamee n)
  round {n} g@(MkGamee arr f) = do
    (ps@[p1,p2,p3], rest) <- pickupsAndRest g
    let dest = calcDest n f ps
    writeArray arr f rest
    Just destNext <- readArray arr dest
     | Nothing => do printLn (dest, "was wrong.")
                     pure g
    writeArray arr dest p1
    writeArray arr p3   destNext
    pure $ MkGamee arr rest

  partial
  calcRound : {n : Int} -> Int -> Gamee n -> IO (Gamee n)
  calcRound 0 g = pure g
  calcRound m g = do
    if (mod m 1000 == 0) then printLn m else pure ()
    round g >>= calcRound (m-1)

  export
  partial
  solve : List Int -> IO ()
  solve xs = do
    g <- createGame xs 1000000
    g' <- calcRound 10000000 g
    renderResult g' >>= putStrLn

puzzleInput : Cups
puzzleInput = [9, 5, 2, 3, 1, 6, 4, 8, 7]

partial
main : IO ()
main = do
  let input = puzzleInput
  -- printLn $ FirstPart.solve input
  solve [9, 5, 2, 3, 1, 6, 4, 8, 7]
  pure ()
