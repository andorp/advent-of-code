module Day25

import Data.Stream
import Debug.Trace

%default total

PbKey : Type
PbKey = Integer

PvKey : Type
PvKey = Integer

LoopSize : Type
LoopSize = Integer

SNumber : Type
SNumber = Integer

oneLoop : SNumber -> (Integer, Integer) -> (Integer, Integer)
oneLoop sn (loopCount, value) = (loopCount + 1, mod (value * sn) 20201227)

partial
findLoopSizes : SNumber -> PbKey -> Stream LoopSize
findLoopSizes s p = mapMaybe (\(l, k) => if k == p then Just l else Nothing) $ iterate (oneLoop s) (0, 1)
  where
    partial
    mapMaybe : (Show b) => (a -> Maybe b) -> Stream a -> Stream b
    mapMaybe f (x :: xs) = case f x of
      Nothing => mapMaybe f xs
      Just y  => y :: mapMaybe f xs

encrypt : SNumber -> LoopSize -> PvKey
encrypt s l = snd $ index (fromInteger l) $ iterate (oneLoop s) (0, 1)

partial
main : IO ()
main = do
  let pbDoor = 9093927
  let pbCard = 11001876
  --let pbDoor = 17807724
  --let pbCard = 5764801
  let lsCard = index 0 $ findLoopSizes 7 pbCard
  let lsDoor = index 0 $ findLoopSizes 7 pbDoor
  printLn lsCard
  printLn lsDoor
  printLn $ encrypt pbDoor lsCard
  printLn $ encrypt pbCard lsDoor
  pure ()
