module Bot
  ( bot
  ) where

import Vindinium

import Prelude(error,(*),(+),(-),undefined,Int,mod,div,(^))
import Control.Applicative ((<$>))
import Control.Arrow ((&&&))
import Control.Monad (return,liftM,(>>=),sequence,mapM,join)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (Reader,asks,runReader)
import Data.Bool (Bool(True,False),(&&))
import Data.Eq (Eq,(==))
import Data.Functor (fmap)
import Data.Function ((.),($),id,flip,const)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Query
import Data.List((!!),length,replicate,map,filter,concat,zip,drop,find)
import Data.Maybe (Maybe(Just,Nothing),fromJust,isNothing,maybe,isJust,fromMaybe)
import Data.Ord (Ord,(>=),(<),(<=))
import Data.PQueue.Max (MaxQueue,toDescList,fromList)

import qualified Data.Text as T
import Data.Tuple (fst,snd)
import Safe (headMay)
import System.IO (IO)
import System.Random (getStdRandom, randomR)
import Text.Show (Show,show)

-- $setup
-- >>> let board = Board 4 [TavernTile,WoodTile,WoodTile,TavernTile,FreeTile,WoodTile,FreeTile,HeroTile (HeroId 2),FreeTile,WoodTile,FreeTile,(MineTile Nothing),FreeTile,FreeTile,HeroTile (HeroId 1),MineTile (Just (HeroId 1))]
-- >>> let hero1 = Hero (HeroId 1) "name" Nothing Nothing (Pos 2 2) 100 0 0 (Pos 3 3) False
-- >>> let game  = Game (GameId "") 1 20 [hero1] board False
-- >>> let state = State game hero1 "" "" ""

type Move = Dir
type BotM = Reader State 
type TileSelector = Tile -> Bool

data Weighted a = Weighted Int a deriving (Show)
instance (Eq a) => Eq (Weighted a) where
  (Weighted wa a) == (Weighted wb b) = wa == wb && a == b
instance (Eq a) => Ord (Weighted a) where
  (Weighted a _) <= (Weighted b _) = a <= b

data Tactic = Tactic T.Text (BotM (Maybe Move))
instance Show Tactic where
  show (Tactic t _) = T.unpack . T.concat $ ["Tactic(",t,")"]
instance Eq Tactic where
  (Tactic a _) == (Tactic b _) = a == b

type TacticPQueue = MaxQueue (Weighted Tactic)

data Strategy = Strategy T.Text (BotM TacticPQueue)
instance Show Strategy where
  show (Strategy t _) = T.unpack . T.concat $ ["Strategy(",t,")"]
instance Eq Strategy where
  (Strategy a _) == (Strategy b _) = a == b  

bot :: Bot
bot = return . runReader dummyBot

strategicBot :: Strategy -> BotM Move
strategicBot (Strategy _ m) = do
  tactics <- toDescList <$> m
  fmap firstMove . mapM (\ (Weighted _ (Tactic _ m)) -> m ) $ tactics
  where
    firstMove :: [Maybe Move] -> Move
    firstMove = fromMaybe Stay . join . find isJust

-- Are these names actually worth the hassle?
runStrategy (Strategy _ m) = runReader m
runTactic (Tactic _ m) = runReader m

-- |
-- >>> runStrategy dummyStrategy state
-- fromDescList [Weighted 10 Tactic(stay)]
dummyStrategy :: Strategy
dummyStrategy = Strategy "dummy" . return $ fromList [Weighted 10 stayTactic]

-- |
-- >>> runTactic stayTactic state
-- Just Stay
stayTactic :: Tactic
stayTactic = Tactic "stay" . return . Just $ Stay

-- |
-- >>> runReader dummyBot state
-- Stay
dummyBot :: BotM Move
dummyBot = strategicBot dummyStrategy

isPassibleTile :: TileSelector
isPassibleTile WoodTile = False
isPassibleTile _        = True

isTavernTile :: TileSelector
isTavernTile TavernTile = True
isTavernTile _          = False

isMineTile :: (Maybe HeroId -> Bool) -> TileSelector
isMineTile selectHid (MineTile hid) = selectHid hid
isMineTile _ _                      = False

isMyMineTile :: BotM TileSelector
isMyMineTile = do
  id <- heroId <$> askMyHero
  return $ isMineTile (== Just id)

isHeroTile :: (HeroId -> Bool) -> TileSelector
isHeroTile selectHid (HeroTile hid) = selectHid hid
isHeroTile _ _  = False

isOpponentTile :: (Hero -> Bool) -> BotM TileSelector
isOpponentTile heroSelect = asks rdr
  where
    rdr s = isHeroTile (heroSelect . fromJust . hero s)
    hero s hid = runReader (askHero hid) s
    
isUnownedMineTile :: TileSelector
isUnownedMineTile = isMineTile isNothing

-- |
-- >>> inBoard board (Pos 0 0)
-- True
-- >>> inBoard board (Pos 3 3)
-- True
-- >>> inBoard board (Pos 4 4)
-- False
inBoard :: Board -> Pos -> Bool
inBoard b (Pos x y) =
  let s = boardSize b
  in x >= 0 && x < s && y >= 0 && y < s

-- |
-- >>> tileAt board (Pos 0 0)
-- Just TavernTile
-- >>> tileAt board (Pos 1 0)
-- Just WoodTile
-- >>> tileAt board (Pos 4 4)
-- Nothing
tileAt :: Board -> Pos -> Maybe Tile
tileAt b p@(Pos x y) =
  if inBoard b p
         then Just $ boardTiles b !! idx
         else Nothing
   where
     idx = y * boardSize b + x

-- |
-- >>> runReader (neighbours 14) state
-- [Pos {posX = 1, posY = 3},Pos {posX = 3, posY = 3},Pos {posX = 2, posY = 2},Pos {posX = 2, posY = 4}]
neighbours :: Int -> BotM [Pos]
neighbours i = do
  b <- askBoard
  return $ sequence [posWest,posEast,posNorth,posSouth] $ indexToPos b i

-- |
-- >>> runReader (validNeighbours 14) state
-- [Pos {posX = 1, posY = 3},Pos {posX = 3, posY = 3},Pos {posX = 2, posY = 2}]
validNeighbours :: Int -> BotM [Pos]
validNeighbours i = do
  hid   <- heroId <$> askMyHero
  b     <- askBoard
  nbs   <- neighbours i
  return $ case tileAt b (indexToPos b i) of
    Just FreeTile     -> filter (inBoard b) nbs
    Just (HeroTile h) | h == hid -> filter (inBoard b) nbs
    _ -> []

-- |
-- >>> runReader (walkableNeighbours 14) state
-- [(14,13,1),(14,15,1),(14,10,1)]
walkableNeighbours :: Int -> BotM [LEdge Int]
walkableNeighbours i = do
  b       <- askBoard
  validNs <- validNeighbours i
  return $ map (\p -> (i,posToIndex b p,1)) validNs

walkableEdges :: BotM [LEdge Int]
walkableEdges = do
  board    <- askBoard
  hid      <- heroId <$> askMyHero  
  idxs     <- askAllIndices
  fmap concat . mapM walkableNeighbours $ idxs

{-
>>> runReader askMoveGraph state
{:
0:TavernTile->[]
1:WoodTile->[]
2:WoodTile->[]
3:TavernTile->[]
4:FreeTile->[(1,8),(1,0),(1,5)]
5:WoodTile->[]
6:FreeTile->[(1,10),(1,2),(1,7),(1,5)]
7:HeroTile (HeroId 2)->[]
8:FreeTile->[(1,12),(1,4),(1,9)]
9:WoodTile->[]
10:FreeTile->[(1,14),(1,6),(1,11),(1,9)]
11:MineTile Nothing->[]
12:FreeTile->[(1,13),(1,8)]
13:FreeTile->[(1,14),(1,9),(1,12)]
14:HeroTile (HeroId 1)->[(1,10),(1,15),(1,13)]
15:MineTile (Just (HeroId 1))->[]
:} -}
askMoveGraph :: BotM (Gr Tile Int)
askMoveGraph = do
  b      <- askBoard
  side   <- askBoardSize
  ledges <- walkableEdges
  let
    lnodes = map (id &&& (boardTiles b !!)) [0,1..((side * side) - 1)]
  return $ mkGraph lnodes ledges

-- |
-- >>> runReader (shortestPath (Pos 2 3) (Pos 0 0)) state
-- [13,12,8,4,0]
shortestPath :: Pos -> Pos -> BotM Path
shortestPath start dest = do
  b <- askBoard
  g <- askMoveGraph
  let
    startIdx = posToIndex b start
    destIdx  = posToIndex b dest
  return $ drop 1 . sp startIdx destIdx $ g
  
-- |
-- >>> runReader (closest isTavernTile (Pos 2 3)) state
-- Just (Pos {posX = 0, posY = 0})
-- >>> runReader (closest isTavernTile (Pos 2 3)) state
-- Just (Pos {posX = 0, posY = 0})
-- >>> runReader (closest isTavernTile (Pos 2 3)) state
-- Just (Pos {posX = 0, posY = 0})
-- >>> runReader (isMyMineTile >>= flip closest (Pos 2 3)) state
-- Just (Pos {posX = 3, posY = 3})
-- >>> runReader (closest isUnownedMineTile (Pos 2 3)) state
-- Just (Pos {posX = 3, posY = 2})
-- >>> runReader (isOpponentTile (const True) >>= flip closest (Pos 2 3)) state
-- Just (Pos {posX = 3, posY = 1}) 
closest :: TileSelector -> Pos -> BotM (Maybe Pos)
closest sel pos = do
  b <- askBoard
  let tiles = filter (sel . snd) . zip [0..] . boardTiles $ b
  return (indexToPos b . fst <$> headMay tiles)
  
-- |
-- >>> runReader (distanceBetween (Pos 2 3) (Pos 1 3)) state
-- Just 1
-- >>> runReader (distanceBetween (Pos 2 3) (Pos 0 0)) state
-- Just 5
-- >>> runReader (distanceBetween (Pos 2 3) (Pos 3 0)) state
-- Nothing
distanceBetween:: Pos -> Pos -> BotM (Maybe Int)
distanceBetween s = fmap distance . shortestPath s
  where
    distance p = Just (length p) >>= (\d -> if d <= 0 then Nothing else Just d)

-- |
-- >>> runReader (tilesWithinRadius isTavernTile 1 (Pos 2 3)) state
-- []
-- >>> runReader (tilesWithinRadius isTavernTile 5 (Pos 2 3)) state
-- [Pos {posX = 0, posY = 0}]
tilesWithinRadius :: TileSelector -> Int -> Pos -> BotM [Pos]
tilesWithinRadius sel rad startP = do
  coordBoard  <- askCoordBoard
  tileSel'    <- selectTile
  return . map fst . filter tileSel' $ coordBoard
  where
    selectTile = asks (\s (p,t) -> sel t && maybe False (<= rad) (runDistanceBetween p s))
    runDistanceBetween p = runReader (distanceBetween startP p)  
    

askBoard :: BotM Board
askBoard = asks (gameBoard . stateGame)

askCoordBoard :: BotM [(Pos,Tile)]
askCoordBoard = do
  board  <- askBoard
  allPos <- map (indexToPos board) <$> askAllIndices
  return $ zip allPos (boardTiles board)

askBoardSize :: BotM Int
askBoardSize = fmap boardSize askBoard

askAllIndices :: BotM [Int]
askAllIndices = fmap (\x -> [0..x^2] ) askBoardSize

allIndices :: Int -> [Int]
allIndices boardSize = [0..( boardSize^2 - 1)]

askMyHero :: BotM Hero
askMyHero = asks stateHero

askHero :: HeroId -> BotM (Maybe Hero)
askHero hid = asks (find ((== hid) . heroId) . gameHeroes . stateGame)

posToIndex :: Board -> Pos -> Node
posToIndex b p@(Pos x y) = idx
  where idx = y * boardSize b + x

indexToPos :: Board -> Node -> Pos
indexToPos b n = Pos (n `mod` side) (n `div` side)
  where side = boardSize b

indexNorth,indexSouth,indexEast,indexWest :: Board -> Node -> Node
indexNorth b = posToIndex b . posNorth . indexToPos b
indexSouth b = posToIndex b . posSouth . indexToPos b
indexEast  b = posToIndex b . posEast  . indexToPos b
indexWest  b = posToIndex b . posWest  . indexToPos b

posNorth,posSouth,posEast,posWest :: Pos -> Pos
posWest (Pos x y) = Pos (x - 1) y
posEast (Pos x y) = Pos (x + 1) y
posSouth  (Pos x y) = Pos x       (y + 1)
posNorth  (Pos x y) = Pos x       (y - 1)
