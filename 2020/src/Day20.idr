module Day20

-- TODO: Clean up this mess. It was a real swamp!

{-
--- Day 20: Jurassic Jigsaw ---
The high-speed train leaves the forest and quickly carries you south. You can even see a desert in the distance! Since you have some spare time, you might as well see if there was anything interesting in the image the Mythical Information Bureau satellite captured.

After decoding the satellite messages, you discover that the data actually contains many small images created by the satellite's camera array. The camera array consists of many cameras; rather than produce a single square image, they produce many smaller square image tiles that need to be reassembled back into a single image.

Each camera in the camera array returns a single monochrome image tile with a random unique ID number. The tiles (your puzzle input) arrived in a random order.

Worse yet, the camera array appears to be malfunctioning: each image tile has been rotated and flipped to a random orientation. Your first task is to reassemble the original image by orienting the tiles so they fit together.

To show how the tiles should be reassembled, each tile's image data includes a border that should line up exactly with its adjacent tiles. All tiles have this border, and the border lines up exactly when the tiles are both oriented correctly. Tiles at the edge of the image also have this border, but the outermost edges won't line up with any other tiles.

For example, suppose you have the following nine tiles:

1951    2311    3079
2729    1427    2473
2971    1489    1171
To check that you've assembled the image correctly, multiply the IDs of the four corner tiles together. If you do this with the assembled tiles from the example above, you get 1951 * 3079 * 2971 * 1171 = 20899048083289.

Assemble the tiles into an image. What do you get if you multiply together the IDs of the four corner tiles?

Your puzzle answer was 54755174472007.

--- Part Two ---
Now, you're ready to check the image for sea monsters.

The borders of each tile are not part of the actual image; start by removing them.

Determine how rough the waters are in the sea monsters' habitat by counting the number of # that are not part of a sea monster. In the above example, the habitat's water roughness is 273.

How many # are not part of a sea monster?

Your puzzle answer was 1692.
-}

import Data.List
import Data.List1
import Data.Strings
import Data.Vect
import Data.SortedMap
import Data.SortedSet
import System.File
import Debug.Trace
import Control.Monad.Identity

%default total

testInput : String
testInput =
"Tile 2311:\
..##.#..#.\
##..#.....\
#...##..#.\
####.#...#\
##.##.###.\
##...#.###\
.#.#.#..##\
..#....#..\
###...#.#.\
..###..###\
\
Tile 1951:\
#.##...##.\
#.####...#\
.....#..##\
#...######\
.##.#....#\
.###.#####\
###.##.##.\
.###....#.\
..#.#..#.#\
#...##.#..\
\
Tile 1171:\
####...##.\
#..##.#..#\
##.#..#.#.\
.###.####.\
..###.####\
.##....##.\
.#...####.\
#.##.####.\
####..#...\
.....##...\
\
Tile 1427:\
###.##.#..\
.#..#.##..\
.#.##.#..#\
#.#.#.##.#\
....#...##\
...##..##.\
...#.#####\
.#.####.#.\
..#..###.#\
..##.#..#.\
\
Tile 1489:\
##.#.#....\
..##...#..\
.##..##...\
..#...#...\
#####...#.\
#..#.#.#.#\
...#.#.#..\
##.#...##.\
..##.##.##\
###.##.#..\
\
Tile 2473:\
#....####.\
#..#.##...\
#.##..#...\
######.#.#\
.#...#.#.#\
.#########\
.###.#..#.\
########.#\
##...##.#.\
..###.#.#.\
\
Tile 2971:\
..#.#....#\
#...###...\
#.#.###...\
##.##..#..\
.#####..##\
.#..####.#\
#..#.#..#.\
..####.###\
..#.#.###.\
...#.#.#.#\
\
Tile 2729:\
...#.#.#.#\
####.#....\
..#.#.....\
....#..#.#\
.##..##.#.\
.#.####...\
####.#.#..\
##.####...\
##..#.##..\
#.##...##.\
\
Tile 3079:\
#.#.#####.\
.#..######\
..#.......\
######....\
####.#..#.\
.#...#.##.\
#.#####.##\
..#.###...\
..#.......\
..#.###...
"

traceIt : (Show a) => a -> a
traceIt x = trace (show x) x

Tile : Type
Tile = Vect 10 (Vect 10 Bool)

TileId : Type
TileId = Int

namespace Parser

  parseTileLine : String -> Maybe (Vect 10 Bool)
  parseTileLine str
    = map (map (\case { '#' => True ; _ => False }))
    $ toVect 10
    $ unpack str

  parseHeader : String -> Maybe TileId
  parseHeader str = do
    let ["Tile", tid] = words str
        | _ => trace ("Parse error: " ++ show str) Nothing
    let is@(_ :: _) = unpack tid
        | _ => trace ("Parse error: " ++ show str) Nothing
    parseInteger $ pack $ init is

  parseTile : List String -> Maybe (TileId, Tile)
  parseTile []        = Nothing
  parseTile [_]       = Nothing
  parseTile (h :: ts) = do
    tid <- parseHeader h
    ls  <- traverse parseTileLine $ take 10 ts
    tl  <- toVect 10 ls
    Just (tid, tl)

  export
  parseInput : String -> Maybe (SortedMap TileId Tile)
  parseInput cnt
    = map SortedMap.fromList
    $ traverse parseTile
    $ toList
    $ split (=="")
    $ lines cnt

Edge : Type
Edge = Vect 10 Bool

EdgeCode : Type
EdgeCode = Bits16

namespace Tile

  public export
  TileCode : Type
  TileCode = Vect 4 EdgeCode

  edgeToCode : Edge -> EdgeCode
  edgeToCode = foldl (\c => \case { True => 2 * c + 1 ; False => 2 * c}) 0

  reverseCodeToEdge : EdgeCode -> Edge
  reverseCodeToEdge = go 10 . cast
    where
      go : (n : Nat) -> Int -> Vect n Bool
      go Z     c = []
      go (S n) c = case (mod c 2) of
        0 => False :: go n (div c 2)
        _ => True  :: go n (div c 2)

  edges : Tile -> Vect 4 Edge
  edges t =
    [ index 0 t
    , map (index 9) t
    , index 9 t
    , map (index 0) t
    ]

  export
  tileCode : Tile -> TileCode
  tileCode = map edgeToCode . edges

  export
  reverseCode : EdgeCode -> EdgeCode
  reverseCode = edgeToCode . reverseCodeToEdge

  export
  rotate : TileCode -> TileCode
  rotate [t,r,b,l] = [reverseCode l, t, reverseCode r, b]

  export
  flipVert : TileCode -> TileCode
  flipVert [t,r,b,l] = [b,reverseCode r,t,reverseCode l]

  export
  flipHor : TileCode -> TileCode
  flipHor [t,r,b,l] = [reverseCode t,l,reverseCode b,r]


namespace FirstPart

  canonicalEdgeCode : EdgeCode -> EdgeCode
  canonicalEdgeCode e = min e (reverseCode e)

  connections : SortedMap TileId TileCode -> TileCode -> (Vect 4 (List TileId))
  connections m tc = map conn tc
    where
      conn : EdgeCode -> List TileId
      conn e = mapMaybe
                (\(tid, tileCode) => case (tileCode == tc, elem e tileCode) of
                    (True,  _)     => Nothing
                    (False, False) => Nothing
                    (False, True)  => Just tid)
             $ SortedMap.toList m

  export
  tileConnections : SortedMap TileId Tile -> SortedMap TileId (Vect 4 (List TileId))
  tileConnections tiles =
    let edges = map (map canonicalEdgeCode . tileCode) tiles
    in map (connections edges) edges

  export
  findCorners : SortedMap TileId (Vect 4 (List TileId)) -> List TileId
  findCorners
    = mapMaybe
        (\(tid, neighbours) => case sum' (map length neighbours) of
          2 => Just tid
          _ => Nothing)
    . SortedMap.toList

  export
  solve : SortedMap TileId Tile -> Int
  solve = product' . findCorners . tileConnections

namespace SecondPart

  data Tr = R | V | H

  Show Tr where
    show R = "R"
    show V = "V"
    show H = "H"

  allTr : List (List Tr)
  allTr =
    [ [V,V], [R],     [R,R],     [R,R,R]
    , [V],   [V,R],   [V,R,R],   [V,R,R,R]
--    , [H],   [H,R],   [H,R,R],   [H,R,R,R]
--    , [H,V], [H,V,R], [H,V,R,R], [H,V,R,R,R]
    ]

  applyTr : TileCode -> Tr -> TileCode
  applyTr tc R = rotate   tc
  applyTr tc V = flipVert tc
  applyTr tc H = flipHor  tc

  transformTile : TileCode -> List Tr -> TileCode
  transformTile = foldl applyTr

  data ED = TE | RE | BE | LE

  tileEdgeCode : ED -> TileCode -> EdgeCode
  tileEdgeCode TE [t,_,_,_] = t
  tileEdgeCode RE [_,r,_,_] = r
  tileEdgeCode BE [_,_,b,_] = b
  tileEdgeCode LE [_,_,_,l] = l

  relativePos : TileCode -> TileCode -> List ((Int, Int), List Tr, TileCode)
  relativePos t1@[t,r,b,l] tc2 =
    let allTc2 = map (\trs => (trs, transformTile tc2 trs)) allTr
        -- TODO: Figure out how to use concatMap here
        tecsT = take 1
              $ mapMaybe
                  (\(tr, tcx) => case tileEdgeCode BE tcx == t of
                    False => Nothing
                    True => Just ((the Int 0, the Int (-1)), tr, tcx))
                  allTc2
        tecsR = take 1
              $ mapMaybe
                  (\(tr, tcx) => case tileEdgeCode LE tcx == r of
                    False => Nothing
                    True => Just ((the Int 1, the Int 0), tr, tcx))
                  allTc2
        tecsB = take 1
              $ mapMaybe
                  (\(tr, tcx) => case tileEdgeCode TE tcx == b of
                    False => Nothing
                    True => Just ((the Int 0, the Int 1), tr, tcx))
                  allTc2
        tecsL = take 1
              $ mapMaybe
                  (\(tr, tcx) => case tileEdgeCode RE tcx == l of
                    False => Nothing
                    True => Just ((the Int (-1), the Int 0), tr, tcx))
                  allTc2
    in tecsT ++ tecsR ++ tecsB ++ tecsL

  tlBr : SortedMap (Int, Int) a -> Maybe ((Int, Int), (Int, Int))
  tlBr i = case keys i of
    []        => Nothing
    (x :: xs) => Just $ foldl (\(n,m) , y => (min n y, max m y)) (x,x) $ xs

  moveCoord : Int -> Int -> SortedMap (Int, Int) a -> SortedMap (Int, Int) a
  moveCoord dx dy = fromList . map (mapFst (\(x,y) => (x+dx, y+dy))) . toList

  -- ### Identity for the do notation
  partial
  buildGrid : SortedMap TileId Tile -> SortedMap (Int, Int) (TileId, List Tr)
  buildGrid tiles = runIdentity $ do
    let conns = tileConnections tiles
    let corners@(_ :: _) = findCorners conns
        | _ => pure empty
    let corner = head corners
    let Just cornerTile = lookup corner tiles
        | _ => pure empty
    let start = [((0,0), corner, [], tileCode cornerTile)]
    let tileMap = buildMap conns start (empty, delete corner (fromList (keys tiles)))
    let Just ((xt,yt), _) = tlBr tileMap
    pure $ moveCoord (-xt) (-yt) tileMap
    where
      buildMap
        :  SortedMap TileId (Vect 4 (List TileId))
        -> List ((Int, Int), TileId, List Tr, TileCode)
        -> (SortedMap (Int, Int) (TileId, List Tr), SortedSet TileId)
        -> SortedMap (Int, Int) (TileId, List Tr)
      buildMap _     [] (m, _) = m
      buildMap conns (((x,y),tid,tr,code) :: rest) (m, ts) =
        case lookup (x,y) m of
          Just _
            => buildMap conns rest (m, delete tid ts)
          Nothing
            => let newEntries : List ((Int, Int), TileId, List Tr, TileCode)
                   newEntries = fromMaybe [] $ do
                    cs <- map (concat . toList) $ lookup tid conns
                    ts <- map (map tileCode) $ traverse (flip lookup tiles) cs
                    let ps = map (relativePos code) ts
                    let entries =
                          zipWith
                            (\ctid => map (\((rx,ry),(ctr, ccode)) => ((x+rx, y+ry), ctid, ctr, ccode)))
                            cs ps
                    Just $ concat entries
               in buildMap conns (newEntries ++ rest) (insert (x,y) (tid, tr) m, delete tid ts)
          -- _ => m -- TODO: Got a nasty bug (Just _, True), (Nothing, _)

  Image : Type -> Type
  Image = SortedMap (Int, Int)

  renderTile : {c , r : Nat} -> Bool -> Vect r (Vect c Bool) -> Image Bool
  renderTile rmv xss
    = fromList
    $ removeBorder rmv
    $ concatMap toList
    $ Vect.zipWith
        (\rowId =>
          Vect.zipWith
            (\colId , b => ((the Int (cast $ finToNat colId), the Int (cast $ finToNat rowId)), b))
            range)
        range
        xss
    where
      removeBorder : Bool -> List ((Int, Int), a) -> List ((Int, Int),a)
      removeBorder False = id
      removeBorder True = mapMaybe
        (\((x,y),a)
          => if (x == 0 || x + 1 == cast c || y == 0 || y + 1 == cast r)
              then Nothing
              else Just ((x-1,y-1),a))

  rotateImage : Image a -> Image a
  rotateImage i = fromMaybe i $ do
    ((0,0), (xb, yb)) <- tlBr i
      | _ => trace "rotateImage" Nothing
    Just $ fromList $ map (mapFst (\(x,y) => (negate y + yb, x))) $ toList i

  flipImageVert : Image a -> Image a
  flipImageVert i = fromMaybe i $ do
    ((0,0), (xb, yb)) <- tlBr i
      | _ => trace "rotateImage" Nothing
    Just $ fromList $ map (mapFst (\(x,y) => (x, negate y + yb))) $ toList i

  flipImageHor : Image a -> Image a
  flipImageHor i = fromMaybe i $ do
    ((0,0), (xb, yb)) <- tlBr i
      | _ => trace "rotateImage" Nothing
    Just $ fromList $ map (mapFst (\(x,y) => (negate x + xb, y))) $ toList i

  applyITr : Image a -> Tr -> Image a
  applyITr i R = rotateImage   i
  applyITr i V = flipImageVert i
  applyITr i H = flipImageHor  i

  transformImage : Image a -> List Tr -> Image a
  transformImage = foldl applyITr

  printImage : Image Bool -> IO ()
  printImage i = do
    let Just (xy, (x,y)) = traceIt $ tlBr i
        | _ => pure ()
    let ls = map
              (\yc =>
                pack $ map
                  (\xc => case lookup (xc, yc) i of
                    Nothing => ' '
                    Just b  => if b then '#' else '.')
                  [ 0 .. x ])
              [ 0 .. y ]
    putStrLn $ unlines ls

  renderImage : SortedMap TileId Tile -> SortedMap (Int, Int) (TileId, List Tr) -> Maybe (Image Bool)
  renderImage tiles pos = do
    images <- traverse
      (\((x,y), (tid, trs)) => do
        tile <- lookup tid tiles
        let img = flip transformImage trs $  renderTile True tile
        Just $ moveCoord (8 * x) (8 * y) img)
      (SortedMap.toList pos)
    Just $ fromList $ concatMap toList images

  seaMonster : Image Bool
  seaMonster
    = fromList
    $ filter (\(k, b) => b)
    $ toList
    $ renderTile False $ the (Vect 3 (Vect 20 Bool)) $
      [ map chr $ fromList $ unpack "                  # "
      , map chr $ fromList $ unpack "#    ##    ##    ###"
      , map chr $ fromList $ unpack " #  #  #  #  #  #   "
      ]
    where
      chr : Char -> Bool
      chr '#' = True
      chr _   = False

  scanImage : Image (Bool, Int) -> Image (Bool, Int)
  scanImage i = fromMaybe i $ do
    ((0,0), (x,y)) <- tlBr i
      | _ => trace "Broken image." Nothing
    matches <- traverse
      (\cy => traverse
        (\cx => do
          let monster = moveCoord cx cy seaMonster
          let allMatch =
                all (\(mx,my) => maybe False fst $ lookup (mx,my) i)
                    (keys monster)
          if allMatch
            then Just $ (map (\k => (k,(True, the Int 1))) (keys monster))
            else Just [])
        [0 .. x])
      [0 .. y]
    let matchVals = fromList $ concat $ concat $ matches
    Just $ mergeWith (\(bi, n) , (_, m) => (bi, n + m)) i matchVals

  countRoughness : Image (Bool, Int) -> Nat
  countRoughness = length . filter (\(_, (b, n)) => b && n == 0) . SortedMap.toList

  allTr2 : List (List Tr)
  allTr2 =
    [ [V,V], [R],     [R,R],     [R,R,R]
    , [V],   [V,R],   [V,R,R],   [V,R,R,R]
    ]

  scanImages : Image Bool -> List Nat
  scanImages i0 =
    let i = map (\x => (x, 0)) i0
    in map (\tr => countRoughness $ scanImage (foldl applyITr i tr))
           allTr2

  export
  partial
  test : SortedMap TileId Tile -> IO ()
  test tiles = do
    let grid = buildGrid tiles
    printLn grid
    let Just img = renderImage tiles grid
    printImage img
    printLn $ scanImages img

partial
main : IO ()
main = do
  Right content <- readFile "day20i1.txt"
    | Left err => putStrLn $ "Error while loading input: " ++ show err
--  let Just tiles = parseInput testInput
  let Just tiles = parseInput content
      | _ => putStrLn "Parse error."
  putStrLn "First part."
  printLn $ FirstPart.solve tiles
  putStrLn "Second part."
  test tiles
