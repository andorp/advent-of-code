module Day22

-- My Goal for today is to learn about certified game state programming.

import System.File
import Data.Strings
import Data.List
import Data.List1
import Data.DPair
import Data.Vect
import Data.Nat
import Debug.Trace

%default total

Card : Type
Card = Int

record Deal where
  constructor MkDeal
  player1 : List1 Card
  player2 : List1 Card

Show Deal where show (MkDeal p1 p2) = show (toList p1, toList p2)

namespace Parser

  parsePlayer : List String -> Maybe (List1 Card)
  parsePlayer xs = case mapMaybe parsePositive xs of
    []        => Nothing
    (x :: xs) => Just (x ::: xs)

  export
  parseInput : String -> Maybe Deal
  parseInput cnt = do
    let (l1, l2) = break (=="") $ lines cnt
    p1 <- parsePlayer l1
    p2 <- parsePlayer l2
    Just $ MkDeal p1 p2

namespace FirstPart

  ||| Abstract Game State
  data GameState : Type where
    NotRunning
      :  GameState
    Running
      : (player1Cards : Nat) -> (player2Cards : Nat)
      -> GameState

  data DrawRes = RoundPlayer1 | RoundPlayer2

  length : List1 a -> Nat
  length l = S (length (tail l))

  data GameCmd : (t : Type) -> GameState -> (t -> GameState) -> Type where
    New  : (d : Deal)
        -> GameCmd () NotRunning (const (Running (length (player1 d)) (length (player2 d))))
    Player1Won : GameCmd () (Running (S c1) 0) (const NotRunning)
    Player2Won : GameCmd () (Running 0 (S c2)) (const NotRunning)

    Draw  : GameCmd (Card, Card) (Running (S c1) (S c2)) (const (Running c1 c2))
    Stock : (Card, Card)
         -> GameCmd DrawRes (Running c1 c2)
                        (\case
                           RoundPlayer1 => Running (S (S c1)) c2
                           RoundPlayer2 => Running c1 (S (S c2)))

    ShowState : GameCmd () state (const state)
    Message   : String -> GameCmd () state (const state)

    Pure  : (res : t)
         -> GameCmd t (stateFn res) stateFn
    (>>=) : GameCmd a state1 stateFn2 ->
            ((res : a) -> GameCmd b (stateFn2 res) stateFn3) ->
            GameCmd b state1 stateFn3

  namespace Loop
    public export
    data GameLoop : (t : Type) -> GameState -> (t -> GameState) -> Type where
      (>>=) : GameCmd a state1 state2Fn ->
              ((res : a) -> Inf (GameLoop b (state2Fn res) state3Fn)) ->
              GameLoop b state1 state3Fn
      Exit : GameLoop () NotRunning (const NotRunning)

  loop : {n1 , n2 : Nat} -> GameLoop () (Running (S n1) (S n2)) (const NotRunning)
  loop {n1} {n2} = do
    ShowState
    (c1, c2) <- Draw
    res <- Stock (c1, c2)
    Message $ "Player 1 plays " ++ show c1
    Message $ "Player 2 plays " ++ show c2
    case res of
      RoundPlayer1 => case n2 of
        Z => do
          Player1Won
          ShowState
          Exit
        (S n1') => do
          Message "Player 1 wins the round!"
          loop
      RoundPlayer2 => case n1 of
        Z => do
          Player2Won
          ShowState
          Exit
        (S n2') => do
          Message "Player 2 wins the round!"
          loop

  export
  crabCombat : Deal -> GameLoop () NotRunning (const NotRunning)
  crabCombat d = do
    New d
    loop

  -- concreate game implementation

  data Fuel = Dry | More (Lazy Fuel)

  partial
  forever : Fuel
  forever = More forever

  ||| Concrete game state
  record State n m where
    constructor MkState
    player1 : Vect n Card
    player2 : Vect m Card

  Show (State n m) where
    show (MkState p1 p2) = show (p1, p2)

  data Game : GameState -> Type where
    GameStart      : Game NotRunning
    GamePlayer1Won : Int -> Game NotRunning
    GamePlayer2Won : Int -> Game NotRunning
    InProgress     : (s : State n m) -> Game (Running n m)

  Show (Game st) where
    show GameStart    = "Start"
    show (GamePlayer1Won s) = "Player 1 won! " ++ show s
    show (GamePlayer2Won s) = "Player 2 won! " ++ show s
    show (InProgress s) = show s

  data GameResult : (t : Type) -> (t -> GameState) -> Type where
    OK : (res : t) -> Game (outstateFn res)
       -> GameResult t outstateFn
    OutOfFuel : GameResult t outstateFn

  ok : (res : t) -> Game (outstateFn res) -> IO (GameResult t outstateFn)
  ok res st = pure (OK res st)

  toVect : (l : List1 a) -> Vect (length l) a
  toVect xs = head xs :: fromList (tail xs)

  append : Vect n a -> Vect m a -> Vect (m + n) a
  append as bs = rewrite plusCommutative m n in as ++ bs

  calcScore : List Int -> Int
  calcScore xs = snd $ foldr (\x , (i, s) => (i + 1, s + (i * x))) (1, 0) xs

  runGameCmd
    :  Fuel
    -> Game instate
    -> GameCmd t instate outstateFn
    -> IO (GameResult t outstateFn)
  runGameCmd fuel state (New d) =
    ok () (InProgress (MkState (toVect $ player1 d) (toVect $ player2 d)))
  runGameCmd fuel (InProgress s) Player1Won =
    ok () (GamePlayer1Won $ calcScore $ toList $ player1 s)
  runGameCmd fuel (InProgress s) Player2Won =
    ok () (GamePlayer2Won $ calcScore $ toList $ player2 s)
  runGameCmd fuel (InProgress s) Draw = do
    let c1 = head $ player1 s
    let c2 = head $ player2 s
    let s' = MkState (tail $ player1 s) (tail $ player2 s)
    ok (c1, c2) (InProgress s')
  runGameCmd fuel (InProgress s) (Stock (c1, c2)) = do
    case compare c1 c2 of
      LT => ok RoundPlayer2 $ InProgress $ record { player2 $= (\xs => append xs [c2, c1]) } s
      EQ => ok RoundPlayer1 $ InProgress $ record { player1 $= (\xs => append xs [c1, c2]) } s
      GT => ok RoundPlayer1 $ InProgress $ record { player1 $= (\xs => append xs [c1, c2]) } s
  runGameCmd fuel state ShowState = do
    printLn state
    ok () state
  runGameCmd fule state (Message m) = do
    putStrLn m
    ok () state
  runGameCmd fuel state (Pure r) = ok r state
  runGameCmd fuel state (cmd >>= next) = do
    OK cmdRes newSt <- runGameCmd fuel state cmd
     | OutOfFuel => pure OutOfFuel
    runGameCmd fuel newSt (next cmdRes)
  runGameCmd Dry _ _ = pure OutOfFuel

  run
    :  Fuel
    -> Game instate
    -> GameLoop t instate outstateFn
    -> IO (GameResult t outstateFn)
  run Dry _ _ = pure OutOfFuel
  run (More fuel) st (cmd >>= next) = do
    OK cmdRes newSt <- runGameCmd fuel st cmd
     | OutOfFuel => pure OutOfFuel
    run fuel newSt (next cmdRes)
  run (More fuel) st Exit = ok () st

  export
  partial
  runGame : Deal -> IO ()
  runGame d = do
    run forever GameStart (crabCombat d)
    pure ()

namespace SecondPart

  record State where
    constructor MkState
    plyr1 : List Card
    plyr2 : List Card

  Eq State where
    MkState p11 p12 == MkState p21 p22 = p11 == p21 && p12 == p22

  Show State where
    show (MkState p1 p2) = show (p1, p2)

  record Gamee where
    constructor MkGamee
    activeState : State
    history : List State

  data Winner = P1W | P2W

  Show Winner where
    show P1W = "Player1"
    show P2W = "Player2"

  checkWinner : State -> Maybe Winner
  checkWinner (MkState [] _) = Just P2W
  checkWinner (MkState _ []) = Just P1W
  checkWinner _              = Nothing

  checkHistory : Gamee -> Maybe Winner
  checkHistory (MkGamee a hs) = if elem a hs then Just P1W else Nothing

  calcScore : State -> Int
  calcScore (MkState [] cs) = snd $ foldr (\x , (i, s) => (i + 1, s + (i * x))) (1, 0) cs
  calcScore (MkState cs []) = snd $ foldr (\x , (i, s) => (i + 1, s + (i * x))) (1, 0) cs
  calcScore _ = -1

  mutual
    partial
    draw : Nat -> Gamee -> IO (Maybe Gamee)
    draw gn (MkGamee s@(MkState (c1::cs1) (c2::cs2)) hs) = do
      let n1 = length cs1
      let n2 = length cs2
      case c1 <= cast n1 && c2 <= cast n2 of
        True => do
          putStrLn "NewGame!"
          (_, w) <- playGame
                      (gn + 1)
                      (MkGamee
                        (MkState
                          (take (fromInteger (cast c1)) cs1)
                          (take (fromInteger (cast c2)) cs2))
                        [])
          case w of
            P1W => pure $ Just $ MkGamee (MkState (cs1 ++ [c1,c2]) cs2) (s::hs)
            P2W => pure $ Just $ MkGamee (MkState cs1 (cs2 ++ [c2,c1])) (s::hs)
        False => do
          case compare c1 c2 of
            LT => pure $ Just $ MkGamee (MkState cs1 (cs2 ++ [c2,c1])) (s::hs)
            EQ => trace "draw.EQ" $ pure $ Just $ MkGamee (MkState cs1 (cs2 ++ [c2,c1])) (s::hs)
            GT => pure $ Just $ MkGamee (MkState (cs1 ++ [c1,c2]) cs2) (s::hs)
    draw _ _ = pure Nothing

    partial
    playGame : Nat -> Gamee -> IO (Gamee, Winner)
    playGame gn g = do
      printLn ("Game", gn, activeState g, length (history g))
      let Nothing = checkHistory g
          | Just w => do
              putStrLn "Infinite recursive game."
              pure (g, w)
      let Nothing = checkWinner (activeState g)
          | Just w => do
              putStrLn "Previous game ended."
              pure (g, w)
      Just g' <- draw gn g
       | Nothing => do
          putStrLn "Draw computed Nothing!"
          pure (g, P1W)
      playGame gn g'

    export
    partial
    run : Deal -> IO ()
    run d = do
      (g, w) <- playGame 1 (MkGamee (MkState (toList $ player1 d) (toList $ player2 d)) [])
      printLn (activeState g, w)
      printLn $ calcScore $ activeState g



testInput : String
testInput =
"Player 1:\
9\
2\
6\
3\
1\
\
Player 2:\
5\
8\
4\
7\
10\
"

recExample : String
recExample =
"Player 1:\
43\
19\
\
Player 2:\
2\
29\
14\
"

partial
main : IO ()
main = do
  Right content <- readFile "day22i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
--  putStrLn content
  let Just deal = parseInput content
  runGame deal
  SecondPart.run deal
