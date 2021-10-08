{-#  OPTIONS_GHC -Wall  #-}
{-#  OPTIONS_GHC -Wno-unused-matches  #-}
{-#  OPTIONS_GHC -Wno-name-shadowing  #-}
{-#  OPTIONS_GHC -Wno-incomplete-patterns  #-}


{-#  LANGUAGE StandaloneDeriving  #-}
{-#  LANGUAGE DeriveGeneric  #-}
{-#  LANGUAGE FlexibleInstances  #-}
{-#  LANGUAGE ScopedTypeVariables  #-}
{-#  LANGUAGE GeneralizedNewtypeDeriving  #-}
{-#  LANGUAGE UndecidableInstances  #-}

module Submission2 where
import Lib
    ( maxBy,
      shortestPaths,
      tabulate,
      wormholesFrom,
      Edge(target, source),
      GameState(..),
      Graph(edgesTo, vertices, edgesFrom),
      Growth(..),
      Order(..),
      Owner(Neutral, Owned),
      Path(..),
      Planet(..),
      PlanetId(..),
      Planets,
      Player(Player1, Player2),
      Ships(..),
      Source(..),
      Target(Target),
      Turns(..),
      Wormhole(..),
      WormholeId(..) )
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe ( catMaybes, fromMaybe, isNothing, fromJust )
import Data.Array ( Ix, Array, (!) )
import Text.Printf ( printf )
import Control.DeepSeq ( NFData )
import GHC.Generics ( Generic )

deriving instance (Integral Growth)
deriving instance (Enum Growth)
deriving instance (Real Growth)

data Strategy
  = Pacifist
  | ZergRush
  | PlanetRankRush
  | Skynet
  deriving (Enum, Bounded, Show, Read)

logic :: Strategy -> GameState -> AIState -> ([Order], Log, AIState)
logic strat gs ai
  = let logic' = case strat of
          Pacifist       -> pacifist
          ZergRush       -> zergRush
          PlanetRankRush -> planetRankRush
          Skynet         -> skynet
    in logic' gs ai {turn = turn ai + 1}

data AIState = AIState
  { turn :: Turns
  , rushTarget :: Maybe PlanetId
  , currentPlanetRank :: Maybe PlanetRanks
  } deriving Generic

initialState :: AIState
initialState = AIState
  { turn = 0
  , rushTarget = Nothing
  , currentPlanetRank = Nothing
  }

type Log = [String]

pacifist :: GameState -> AIState -> ([Order], Log, AIState)
pacifist _ ai = ([], ["Do no harm."], ai)

enemyPlanet :: Planet -> Bool
enemyPlanet (Planet (Owned Player2) _ _) = True
enemyPlanet _                            = False

findEnemyPlanet :: GameState -> Maybe PlanetId
findEnemyPlanet (GameState ps _ _)
  | null ePlanets          = Nothing
  | otherwise              = Just (fst (head ePlanets))
  where
    ePlanets = M.toList (M.filter enemyPlanet ps)

send :: WormholeId -> Maybe Ships -> GameState -> [Order]
send wId mShips st
  | not (ourPlanet planet) = []
  | isNothing mShips || fromJust mShips > totalShips = [Order wId totalShips]
  | otherwise = [Order wId (fromJust mShips)]
 where
  Wormhole (Source src) _ _ = lookupWormhole wId st
  planet@(Planet _ totalShips _) = lookupPlanet src st


shortestPath :: PlanetId -> PlanetId -> GameState
             -> Maybe (Path (WormholeId, Wormhole))
shortestPath src dst st
  = case filter ((== dst) . target) (shortestPaths st src) of
      [] -> Nothing
      (x : _) -> Just x

ourPlanet :: Planet -> Bool
ourPlanet (Planet (Owned Player1) _ _) = True
ourPlanet _ = False

ourPlanets :: GameState -> Planets
ourPlanets (GameState ps _ _) = M.filter ourPlanet ps

lookupWormhole :: WormholeId -> GameState -> Wormhole
lookupWormhole wId (GameState _ wormholes _)
  = wormholes M.! wId

lookupPlanet :: PlanetId -> GameState -> Planet
lookupPlanet pId (GameState planets _ _)
  = planets M.! pId

attackFromAll :: PlanetId -> GameState -> [Order]
attackFromAll targetId gs
  = concat [send wId Nothing gs | wId <- whIds]
  where
    ourPlanetIds :: [PlanetId]
    ourPlanetIds = map fst (M.toList (ourPlanets gs))

    shortestPaths :: [Path (WormholeId, Wormhole)]
    shortestPaths = catMaybes [shortestPath ourId targetId gs | ourId <- ourPlanetIds]

    whIds :: [WormholeId]
    whIds =  [(fst . last) whs | (Path _ whs) <- shortestPaths]


zergRush :: GameState -> AIState
         -> ([Order], Log, AIState)
zergRush gs ai
  | isNothing targetId || not (ourPlanet (lookupPlanet (fromJust targetId) gs))
    = ([], ["zergRush - no current target"], ai {rushTarget = findEnemyPlanet gs})
  | otherwise = (attackFromAll (fromJust targetId) gs, ["zergRush - target exists"], ai)
  where
    targetId = rushTarget ai

newtype PageRank = PageRank Double
  deriving (Num, Eq, Ord, Fractional)

type PageRanks pageId = Map pageId PageRank

instance Show PageRank where
  show (PageRank p) = printf "%.4f" p

initPageRanks :: (Graph g e pageId, Ord pageId)
              => g -> PageRanks pageId
initPageRanks g = M.fromList [ (p, PageRank (1 / fromIntegral n))
                             | p <- ps ]
  where ps = vertices g
        n  = length ps

example1 :: [(String, String, Integer)]
example1 = [("a","b",1), ("a","c",1), ("a","d",1),
            ("b","a",1), ("c","a",1), ("d","a",1), ("c","d",1)]

initPageRank' :: Map pageId a -> PageRanks pageId
initPageRank' ps
  = M.map (const prk) ps
  where
    prk = 1 / fromIntegral (M.size ps)

nextPageRank :: (Ord pageId, Edge e pageId, Graph g e pageId) =>
  g -> PageRanks pageId -> pageId -> PageRank
nextPageRank g pr i = (1 - d) / n + d * sum [ pr M.! j / t j
                                            | j <- s i ]
 where
  d   = 0.85
  n   = fromIntegral (length (vertices g))
  t j = fromIntegral (length (edgesFrom g j))
  s i = map source (edgesTo g i)

nextPageRanks :: Ord pageId => Graph g e pageId =>
  g -> PageRanks pageId -> PageRanks pageId
nextPageRanks g pr = M.mapWithKey (const . nextPageRank g pr) pr

pageRanks :: (Ord pageId, Graph g e pageId) => g -> [PageRanks pageId]
pageRanks g = iterate (nextPageRanks g) (initPageRanks g)

pageRank :: (Ord pageId, Graph g e pageId) =>
  g -> PageRanks pageId
pageRank g = pageRanks g !! 200

nextPageRank' :: (Ord pageId, Edge e pageId, Graph g e pageId) =>
  g -> PageRanks pageId -> PageRank -> pageId -> PageRank -> Maybe PageRank
nextPageRank' g pr k i pri
  | abs (pri - pri') < k  = Nothing
  | otherwise             = Just pri'
 where
   pri' = nextPageRank g pr i

nextPageRanks' :: Ord pageId => Graph g e pageId =>
  g -> PageRank -> PageRanks pageId -> Maybe (PageRanks pageId)
nextPageRanks' g k pr = case M.mapAccumWithKey nextPageRank'' True pr of
                           (True,  pr)  -> Nothing
                           (False, pr') -> Just pr'
  where
    nextPageRank'' converged i pri = case nextPageRank' g pr k i pri of
                            Nothing   -> (converged, pri)
                            Just pri' -> (False, pri')

pageRanks' :: (Ord pageId, Graph g e pageId)
  => g -> PageRank -> [PageRanks pageId]
pageRanks' g k = iterateMaybe (nextPageRanks' g k) (initPageRanks g)

iterateMaybe :: (a -> Maybe a) -> a -> [a]
iterateMaybe f x = x : maybe [] (iterateMaybe f) (f x)

pageRank' :: (Ord pageId, Graph g e pageId) =>
  g -> PageRanks pageId
pageRank' g
  = last (take numItr (pageRanks' g k))
  where
    k = 0.0001
    numItr = 200


example2 :: GameState
example2 = GameState planets wormholes fleets where
  planets = M.fromList
    [ (PlanetId 0, Planet (Owned Player1) (Ships 300) (Growth 7))
    , (PlanetId 1, Planet Neutral         (Ships 200) (Growth 2))
    , (PlanetId 2, Planet Neutral         (Ships 150) (Growth 3))
    , (PlanetId 3, Planet Neutral         (Ships 30)  (Growth 6))
    ]
  wormholes = M.fromList
    [ (WormholeId 0, Wormhole (Source 0) (Target 1) (Turns 1))
    , (WormholeId 1, Wormhole (Source 0) (Target 2) (Turns 1))
    , (WormholeId 2, Wormhole (Source 0) (Target 3) (Turns 1))
    , (WormholeId 3, Wormhole (Source 1) (Target 0) (Turns 1))
    , (WormholeId 4, Wormhole (Source 2) (Target 0) (Turns 1))
    , (WormholeId 5, Wormhole (Source 3) (Target 0) (Turns 1))
    , (WormholeId 6, Wormhole (Source 2) (Target 3) (Turns 1))
    ]
  fleets = []

newtype PlanetRank = PlanetRank Double
  deriving (Num, Eq, Ord, Fractional)

type PlanetRanks = Map PlanetId PlanetRank

instance Show PlanetRank where
  show (PlanetRank p) = printf "%.4f" p

initPlanetRanks :: GameState -> PlanetRanks
initPlanetRanks g = M.fromList [ (p, PlanetRank (1 / fromIntegral n))
                               | p <- ps ]
  where ps = vertices g
        n  = length ps

planetRank :: GameState -> PlanetRanks
planetRank g = planetRanks g !! 200

planetRanks :: GameState -> [PlanetRanks]
planetRanks g = iterate (nextPlanetRanks g) (initPlanetRanks g)

nextPlanetRanks :: GameState -> PlanetRanks -> PlanetRanks
nextPlanetRanks g pr = M.mapWithKey (const . nextPlanetRank g pr) pr

nextPlanetRank :: GameState -> PlanetRanks
               -> PlanetId -> PlanetRank
nextPlanetRank g@(GameState planets _ _) pr i =
 (1 - d) / n + d * sum [ pr M.! j * growth i / growths j
                       | j <- targets i ]
 where
  d   = 0.85
  n   = fromIntegral (length planets)

  growth :: PlanetId -> PlanetRank
  growth i  = (\(Planet _ _ g) -> fromIntegral g)
                                  (planets M.! i)
  targets :: PlanetId -> [PlanetId]
  targets i = map (target . snd) (edgesFrom g i)

  growths :: PlanetId -> PlanetRank
  growths j
    = sum (map (growth . source . snd) (edgesTo g j))


checkPlanetRanks :: PlanetRanks -> PlanetRank
checkPlanetRanks = sum . M.elems

planetRankRush :: GameState -> AIState
               -> ([Order], Log, AIState)
planetRankRush gs ai
  | currTargExists = (attackFromAll (fromJust currTarg) gs, ["planetRankRush - target exists"], ai {currentPlanetRank = Just pRank})
  | otherwise      = ([], ["planetRankRush - no current target"], ai {currentPlanetRank = Just pRank, rushTarget = bstTargP})
  where
    pRank = fromMaybe (planetRank gs) (currentPlanetRank ai)
    currTarg = rushTarget ai
    currTargExists = maybe False (not . ourPlanet . flip lookupPlanet gs) currTarg
    bstTargP = if null bstPs then Nothing else Just (head bstPs)
    bstPs = findBestValues [] Nothing (M.toList pRank)

findBestValues :: Ord a => [b] -> Maybe a -> [(b, a)] -> [b]
findBestValues ks _ [] = ks
findBestValues ks Nothing ((k, v) : kvs) = findBestValues (k : ks) (Just v) kvs
findBestValues ks (Just prk) ((k, v) : kvs)
  | v < prk   = findBestValues ks (Just prk) kvs
  | v > prk   = findBestValues [k] (Just v) kvs
  | otherwise = findBestValues (k : ks) (Just v) kvs

targetPlanets :: GameState -> Source -> [(PlanetId, Ships, Growth)]
targetPlanets st s
  = map (planetDetails . target) (M.elems (wormholesFrom s st))
  where
    planetDetails :: PlanetId -> (PlanetId, Ships, Growth)
    planetDetails pId = (pId, ships, growth)
      where Planet _ ships growth = lookupPlanet pId st


skynet :: GameState -> AIState
       -> ([Order], Log, AIState)

skynet gs ai
  | isNothing mSrc = ([], ["Waiting to own a planet"], ai)
  | otherwise      = (order, ["Attack"], ai)
  where
    ourPs = ourPlanets gs

    -- gets list of owned planet ids with highest ships garrisoned
    psWithMostShips = findBestValues [] Nothing pIdShips
    pIdShips = map (\pId -> (pId, shipsOnPlanet gs pId)) (M.keys ourPs)

    -- source planet is the owned planet id with the most ships
    mSrc = if null psWithMostShips then Nothing else Just (head psWithMostShips)
    src = fromJust mSrc

    srcShips = shipsOnPlanet gs src
    trgPs = targetPlanets gs (Source src)

    (_, attackPs) = bknapsack'' trgPs srcShips
    sPaths = catMaybes [shortestPath src tId gs | tId <- attackPs]
    whIds = [(fst . last) e | (Path _ e) <- sPaths]
    order = if null whIds then [] else send (head whIds) (battleShips srcShips) gs

    shipsOnPlanet :: GameState -> PlanetId -> Ships
    shipsOnPlanet st pId = ships
      where Planet _ ships _ = lookupPlanet pId st

    battleShips :: Ships -> Maybe Ships
    battleShips (Ships s) = Just (Ships (div s (div 5 2)))

    bknapsack'' :: forall name weight value .
      (Ord name, Ix weight, Ord weight, Num weight,
        Ord value, Num value) =>
      [(name, weight, value)] -> weight -> (value, [name])
    bknapsack'' wvs c = table ! (c, length wvs)
      where
        table :: Array (weight, Int) (value, [name])
        table = tabulate ((0, 0), (c, length wvs)) mbknapsack

        mbknapsack :: (weight, Int) -> (value, [name])
        mbknapsack (0, _) = (0, [])
        mbknapsack (_, 0) = (0, [])
        mbknapsack (c, idx)
          | w > c     = (nV, nNs)
          | otherwise = maxBy fst (incV + v, n : incNs) (nV, nNs)
          where
            (n, w, v)     = wvs !! (idx - 1)
            (incV, incNs) = table ! (c - w, idx - 1)
            (nV, nNs)     = table ! (c, idx - 1)


deriving instance Generic PlanetRank
deriving instance Generic PageRank

instance NFData PageRank
instance NFData PlanetRank
