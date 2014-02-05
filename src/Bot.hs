module Bot
  ( bot
  ) where

import Vindinium

import Prelude(error,(*),(+),(-),undefined,Int,mod,div)
import Control.Applicative ((<$>))
import Control.Arrow ((&&&))
import Control.Monad (return,liftM,(>>=))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (Reader,asks,runReader)
import Data.Bool (Bool(True,False),(&&))
import Data.Eq ((==))
import Data.Functor (fmap)
import Data.Function ((.),($),id,flip,const)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Query
import Data.Maybe (Maybe(Just,Nothing),fromJust,isNothing)
import Data.Ord ((>=),(<))
import Data.List((!!),length,replicate,map,filter,concatMap,zip,drop,find)
import Data.Tuple (fst,snd)
import Safe (headMay)
import System.IO (IO)
import System.Random (getStdRandom, randomR)


-- $setup
-- >>> let board = Board 4 [TavernTile,WoodTile,WoodTile,TavernTile,FreeTile,WoodTile,FreeTile,HeroTile (HeroId 2),FreeTile,WoodTile,FreeTile,(MineTile Nothing),FreeTile,FreeTile,HeroTile (HeroId 1),MineTile (Just (HeroId 1))]
-- >>> let hero1 = Hero (HeroId 1) "name" Nothing Nothing (Pos 2 2) 100 0 0 (Pos 3 3) False
-- >>> let game  = Game (GameId "") 1 20 [hero1] board False
-- >>> let state = State game hero1 "" "" ""

type BotM = Reader State 
type TileSelector = Tile -> Bool

bot :: Bot
bot = undefined

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
-- 1
-- >>> runReader (distanceBetween (Pos 2 3) (Pos 0 0)) state
-- 5
distanceBetween:: Pos -> Pos -> BotM Int
distanceBetween s = fmap length . shortestPath s

askMoveGraph :: BotM (Gr Tile Int)
askMoveGraph = do
  b    <- askBoard
  me   <- askMyHero
  side <- askBoardSize
  let
    n = (side * side) - 1
    lnodes = map (id &&& (boardTiles b !!)) [0,1..n]
    ledges = walkableEdges b (heroId me)

  return $ mkGraph lnodes ledges
         
walkableEdges :: Board -> HeroId -> [LEdge Int]
walkableEdges b hid = concatMap walkableNeighbours [0,1..n]
  where walkableNeighbours i = map (\t@(p,d) -> (i, posToIndex b p, d)) (validNeighBours i)
        validNeighBours i =
          case tileAt b (indexToPos b i) of
            Just FreeTile     -> filter (\ln@(i,_) -> (inBoard b i)) $ neighBours i
            Just (HeroTile h) | h == hid -> filter (\ln@(i,_) -> (inBoard b i)) $ neighBours i
            _ -> []
        side = boardSize b
        n = (side * side) - 1
        neighBours i = [--Positions of neighbours and travel distance of 1
                        (Pos ((i `mod` side) - 1) (i `div` side), 1), --West
                        (Pos ((i `mod` side) + 1) (i `div` side), 1), --East
                        (Pos (i `mod` side) ((i `div` side) - 1), 1), --North
                        (Pos (i `mod` side) ((i `div` side) + 1), 1)] --South

shortestPath :: Pos -> Pos -> BotM Path
shortestPath start dest = do
  b <- askBoard
  g <- askMoveGraph
  let
    startIdx = posToIndex b start
    destIdx  = posToIndex b dest
  return $ drop 1 . sp startIdx destIdx $ g
  

askBoard :: BotM Board
askBoard = asks (gameBoard . stateGame)

askBoardSize :: BotM Int
askBoardSize = fmap boardSize askBoard

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
