module Box where

import Data.List
import Data.Either
import Data.Maybe

type Name = Integer
type Dim  = [Name]
data Dir  = Up | Down
  deriving (Eq, Show)
type Side = (Name, Dir)

sides :: Dim -> [Side]
sides d = concat [[(x,Up), (x,Down)] | x <- d]

mirror :: Dir -> Dir
mirror Up = Down
mirror Down = Up

oppSide :: Side -> Side
oppSide (x, dir) = (x, mirror dir)

{- New Boxing -}
data Box t = Box {
   boxSingleSide :: Maybe Side,
   boxDim        :: Dim,
   boxMap        :: [(Side, t)]
}
  deriving (Eq, Show)

mapBox :: (Side -> t -> t) -> Box t -> Box t
mapBox f (Box ms d' vs) = Box ms d' fvs
    where fvs = [(s, f s v) | (s@(x,_), v) <- vs]

getSide :: Box t -> Side -> t
getSide (Box s0 d vs) s@(x,dir) =
  case lookup s vs of
    Just v -> v
    Nothing -> if x `elem` d
                 then error $ "getSide: missing expected side " ++ show s
               else if Just s == s0
                 then error $ "getSide: missing single side " ++ show s
               else error $ "getSide: side not expected " ++ show s

boxSides :: Box t -> [Side]
boxSides box@(Box s d _) =
  (case s of Just s -> [s]; Nothing -> []) ++ sides d

isOpenBox :: Box t -> Bool
isOpenBox (Box (Just _) _ _) = True
isOpenBox _                  = False


openBox :: Show t => Side -> Box t -> Box t
openBox s0@(x,dx) (Box Nothing d vs)
    | x `elem` d = Box (Just (oppSide s0)) (delete x d) vs'
    | otherwise  = error $ "openBox t: " ++ show x ++ " not in " ++ show d
  where vs' = [(s,v) | (s,v) <- vs, s /= s0]
openBox _ (Box (Just s) _ _) =
    error $ "openBox t : already open on side " ++ show s

boxBoundary :: Show t => Box t -> Box t
boxBoundary (Box (Just _) d vs) = Box Nothing d vs
boxBoundary b = error $ "openBox t : already a boundary " ++ show b


-- TODO: rewrite mkBox using addBox t or funMkBox
mkBox :: Maybe (Side,t) -> [(Name, (t, t))] -> Box t
mkBox sv xvvs = Box s0 d (sv0 ++ concat vvs) where
    (s0, sv0) = case sv of Just (s, v) -> (Just s, [(s, v)])
                           Nothing     -> (Nothing, [])
    d         = map fst xvvs
    vvs       = [ [((x,Down),vDown), ((x,Up),vUp)]
                | (x, (vDown, vUp)) <- xvvs]


funMkBox :: Maybe Side -> Dim -> (Side -> t) -> Box t
funMkBox s d f = Box s d [(s, f s) | s <- ss] where
  ss = (case s of Just s -> [s]
                  Nothing -> []) ++ (sides d)

add2Sides :: (Name,(t, t)) -> Box t -> Box t
add2Sides (x,(vDown,vUp)) (Box s0 d vs) =
    Box s0 (x:d) (((x,Down),vDown):((x,Up),vUp):vs)

addSingleSide :: Show t => (Side, t) -> Box t -> Box t
addSingleSide (s, v) (Box Nothing d vs) = (Box (Just s) d ((s,v):vs))
addSingleSide _ b = error $ "addSingleSide: not boundary " ++ show b


-- assumes homogeneity of the list
listBox :: Box [t] -> [Box t]
listBox (Box s0 d vss) =  [Box s0 d bc | bc <- bcs] where
    bcs = transpose [[(s, v) | v <- vs] | (s, vs) <- vss]
