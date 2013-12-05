{-# LANGUAGE PatternGuards, TupleSections #-}

module Eval where

import Control.Arrow hiding (app)
import Control.Applicative ((<$>))
import Data.List
import Data.Either
import Data.Maybe
import Box
import Debug.Trace

import Core

dimeq :: Dim -> Dim -> Bool
dimeq d d' = sort (nub d) == sort (nub d')

gensym :: Dim -> Name
gensym [] = 0
gensym xs = maximum xs + 1

gensyms :: Dim -> [Name]
gensyms d = x : (gensyms (x : d)) where x = gensym d

-- all *very* hackish
type Mor = ([(Name, Either Dir Name)], Dim)
-- I -> J u {0,1}

identity :: Dim -> Mor
identity d = ([(i, Right i) | i <- d], d)

dom :: Mor -> Dim               -- *not* the names f is defined on
dom (al,cd) = map fst al

cod :: Mor -> Dim
cod (al,co) = co

def :: Mor -> Dim
def (al, co)  = [ i | (i, Right _) <- al ]

ndef :: Mor -> Dim
ndef (al, _)  = [ i | (i, Left _) <- al ]

-- update f x y is (f, x=y) (x and y fresh)
update :: Mor -> Name -> Name -> Mor
update (al,co) x y = ((x,Right y):al, y:co)

-- rename x to y in v. assumes x and y are fresh to d.
rename :: Dim -> Val -> Name -> Name -> Val
rename d v x y = v `res` update (identity d) x y

im :: Mor -> Dim
im (al, _) = [ y | (_, Right y) <- al ]

ap :: Mor -> Name -> Either Dir Name
f@(al, _) `ap` i = case lookup i al of
  Just x    -> x
  otherwise -> error $ "ap: " ++ show f ++ " undefined on " ++ show i

-- Supposes that f is defined on i
dap :: Mor -> Name -> Name
f `dap` i = case f `ap` i of
  Left b -> error "dap: undefined"
  Right x -> x

comp :: Mor -> Mor -> Mor -- use diagram order!
comp f g = ([(i, (f `ap` i) >>= (g `ap`))| i <- dom f], cod g)

-- Assumption: d <= c
-- Compute degeneracy map.
deg :: Dim -> Dim -> Mor
deg d c | d /= nub d = error $ "deg " ++ show d ++ " and " ++ show c
        | otherwise  = (map (\i -> (i, Right i)) d, c)

-- Compute the face map.
-- (i=b) : d -> d-i
face :: Dim -> Side -> Mor
face d (i, b) = ((i, Left b):[(j, Right j) | j <- di], di)
  where di | i `elem` d = delete i d
           | otherwise  = error $ "face " ++ show i ++ " not in " ++ show d

-- If f : I->J and f defined on i, then (f-i): I-i -> J-fi
-- If f : I->J and f not defined on i, then (f-i): I-i -> J
minus :: Mor -> Name -> Mor
(f@(al,co)) `minus` i = ([(j,v)| (j,v) <- al, i/=j] , co')
  where co' | i `elem` def f = delete (f `dap` i) co
            | otherwise = co

direq :: Either Dir Name -> Dir -> Bool
Left Down `direq` Down = True
Left Up `direq` Up = True
_ `direq` _ = False

data KanType = Fill | Com
  deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VId Val Val Val
         | Path Val             -- tag values which are paths
         | VExt Name Dim Val Val Val Val -- has dimension (name:dim);
                                         -- vals of dimension dim
         | VPi Val Val
         | VApp Val Val         -- not needed for closed terms
         | VInh Val
         | VInc Val
         | VSquash Name Dim Val Val  -- has dimension (name:dim); vals
                                     -- of dimension dim
         | VCon Ident [Val]
         | Kan KanType Dim Val VBox
         | VLSum [(Ident,[Val])]
         | VEquivEq Name Dim Val Val Val Val Val -- of type U of dimension name:dim
           -- VEquivEq x d a b f s t where
         | VPair Name Val Val -- of type VEquiv

--         | VInhRec Dim Val Val Val Val -- not needed for closed terms

--         | Res Val Mor              -- not needed for closed terms

--         | VBranch [(Ident,Ter)] Env
--         | VBranch [(Ident,Val)]
--         | VTrans Val Val Val   -- ?? needed
  deriving (Show, Eq)

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

freeNames :: Val -> [Name]
freeNames VU             = []
freeNames (Ter t e)      = freeNamesTer t `union` freeNamesEnv e
freeNames (VId v1 v2 v3) = unionsMap freeNames [v1,v2,v3]
freeNames (Path v)       = freeNames v
freeNames (VInh v)       = freeNames v
freeNames (VInc v)       = freeNames v
freeNames (VPi v1 v2)    = unionsMap freeNames [v1,v2]
freeNames (VApp v1 v2)   = unionsMap freeNames [v1,v2]
freeNames (VCon _ vs)    = unionsMap freeNames vs
freeNames (VLSum xs)     = unions [ unionsMap freeNames vs | (_,vs) <- xs ]
freeNames (VSquash n d v1 v2)    =
  [n] `union` d `union` unionsMap freeNames [v1,v2]
freeNames (VExt n d v1 v2 v3 v4) =
  [n] `union` d `union` unionsMap freeNames [v1,v2,v3,v4]
freeNames (Kan _ d v box@(Box s0 bd _)) =
  d `union` freeNames v `union` bd `union` boxnames where
      boxnames = unions [freeNames (getSide box s) | s <- boxSides box]
freeNames (VEquivEq n d v1 v2 v3 v4 v5) =
  [n] `union` d `union` unionsMap freeNames [v1,v2,v3,v4,v5]
freeNames (VPair n v1 v2) = [n] `union` unionsMap freeNames [v1,v2]

-- Terms do not rely on names?
freeNamesTer :: Ter -> [Name]
freeNamesTer _ = []

freeNamesEnv :: Env -> [Name]
freeNamesEnv Empty       = []
freeNamesEnv (Pair e v)  = freeNamesEnv e `union` freeNames v
freeNamesEnv (PDef ts e) = unionsMap freeNamesTer ts `union` freeNamesEnv e

fstVal, sndVal :: Val -> Val
fstVal (VPair _ a _) = a
fstVal x             = error $ "fstVal: " ++ show x
sndVal (VPair _ _ v) = v
sndVal x             = error $ "fstVal: " ++ show x

-- assumes x is not in d
pathWith :: Dim -> Name -> Val -> Val
pathWith d x v = Path $ rename d v x (gensym d)

unPath :: Val -> Val
unPath (Path v) = v
unPath v        = error $ "unPath: " ++ show v

-- assumes x is not in d and v is a path
unPathAs :: Dim -> Name -> Val -> Val
unPathAs d x (Path v) = rename d v (gensym d) x
unPathAs _ _ v        = error $ "unPath: " ++ show v

data Env = Empty
         | Pair Env Val
         | PDef [Ter] Env
  deriving (Eq,Show)

upds :: Env -> [Val] -> Env
upds = foldl Pair

look :: Int -> Dim -> Env -> Val
look 0 d (Pair _ u)     = u
look k d (Pair s _)     = look (k-1) d s
look k d r@(PDef es r1) = look k d (upds r1 (evals d r es))

ter :: Dim -> Val -> Val
ter d (Ter t e) = eval d e t

evals :: Dim -> Env -> [Ter] -> [Val]
evals d e = map (eval d e)

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty = Empty
mapEnv f (Pair e v) = Pair (mapEnv f e) (f v)
mapEnv f (PDef ts e) = PDef ts (mapEnv f e)

eval :: Dim -> Env -> Ter -> Val
eval _ _ U       = VU
eval d e (Var i) = look i d e
eval d e (Id a a0 a1) = VId (eval d e a) (eval d e a0) (eval d e a1)
eval d e (Refl a)  = Path $ eval d e a `res` deg d (gensym d : d)

eval d e (Trans c p t) =
  case eval d e p of
    Path pv -> com (x:d) (app (x:d) (eval (x:d) e' c) pv) box
    pv -> error $ "eval: trans-case not a path value:" ++ show pv -- ??
  where x = gensym d
        e' = mapEnv (`res` deg d (x:d)) e
        box = mkBox (Just ((x,Down), eval d e t)) []

eval d e (TransInv c p t) =
  case eval d e p of
    Path pv -> com (x:d) (app (x:d) (eval (x:d) e' c) pv) box
    pv -> error $ "eval: trans-case not a path value:" ++ show pv -- ??
  where x = gensym d
        e' = mapEnv (`res` deg d (x:d)) e
        box = mkBox (Just ((x,Up), eval d e t)) []

-- TODO: throw out v, not needed?
eval d e (J a u c w v p) = case eval d e p of
  Path pv ->
    --trace ("J: A: " ++ show (eval dxy exy a) ++ "\n theta:" ++ show theta ++"\n omega: " ++ show omega)
               com dy (app dy (app dy cv omega) sigma) box
    where
      x:y:_ = gensyms d      -- pv is in x:d
      dy = y:d               -- Cyril: no need for z thanks to pathWith
      dxy = y:x:d
      uv = eval d e u
      ux = uv `res` deg d (x:d)
      uy = uv `res` deg d dy
      exy = mapEnv (`res` deg d dxy) e
      ey = mapEnv (`res` deg d dy) e
      theta = fill dxy (eval dxy exy a)
              (mkBox (Just ((x,Down), uy)) [(y,(ux,pv))]) -- y:x:d
      sigma = pathWith dy x theta                         -- y:d
      omega = theta `res` face dxy (x,Up)                 -- y:d
      cv = eval dy ey c                                   -- y:d
      box = mkBox (Just ((y,Down), eval d e w)) []
  pv -> error $ "eval: J on a non path value:" ++ show pv

eval d e (JEq a u c w) = pathWith d y filled
  where
    x:y:_ = gensyms d
    dy = y:d
    dxy = y:x:d
    exy = mapEnv (`res` deg d dxy) e
    ey = mapEnv (`res` deg d dy) e
    uv = eval d e u
    ux = uv `res` deg d (x:d)
    uy = uv `res` deg d dy
    theta = fill dxy (eval dxy exy a) (mkBox (Just ((x,Down),uy)) [(y,(ux,ux))])
    sigma = pathWith dy x theta
    omega = theta `res` face dxy (x,Up)
    cv = eval dy ey c
    box = mkBox (Just ((y,Down), eval d e w)) []
    filled = fill dy (app dy (app dy cv omega) sigma) box

    -- x = gensym d
    -- dx = x:d
    -- wv = eval d e w
    -- uv = eval d e u
    -- reflu = Path $ uv `res` deg d dx
    -- ex = map (`res` (deg d dx) e)
    -- cv = eval dx ex c

eval d e (Ext b f g p) =
  Path $ VExt (gensym d) d (eval d e b) (eval d e f) (eval d e g) (eval d e p)
eval d e (Pi a b)  = VPi (eval d e a) (eval d e b)
eval d e (Lam t)   = Ter (Lam t) e -- stop at lambdas
eval d e (App r s) = app d (eval d e r) (eval d e s)

eval d e (Inh a) = VInh (eval d e a)
eval d e (Inc t) = VInc (eval d e t)
eval d e (Squash r s) = Path $ VSquash (gensym d) d (eval d e r) (eval d e s)
eval d e (InhRec b p phi a) =
  inhrec d (eval d e b) (eval d e p) (eval d e phi) (eval d e a)
eval d e (Where t def) = eval d (PDef def e) t
--  where e' = map (eval d e') (reverse def) ++ e -- use Haskell's laziness
--eval d e (Where t def) = eval d (map (eval d e) def ++ e) t
eval d e (Con name ts) = VCon name (map (eval d e) ts)
-- eval d e (Branch alts) = VBranch alts e
eval d e (Branch alts) = Ter (Branch alts) e
  -- VBranch $ map (\(n,t) -> (n, eval d e t)) alts
eval d e (LSum ntss) = --trace ("eval lsum " ++ show ntss ++ "\n")
                       --  VLSum $ map (\(n,ts) -> (n, map (eval d e) ts)) ntss
                         Ter (LSum ntss) e

eval d e (EquivEq a b f s t) =  -- TODO: are the dimensions of a,b,f,s,t okay?
  Path $ VEquivEq (gensym d) d (eval d e a) (eval d e b)
                  (eval d e f) (eval d e s) (eval d e t)

inhrec :: Dim -> Val -> Val -> Val -> Val -> Val
inhrec d _ _ phi (VInc a)             = app d phi a
inhrec d' b p phi (VSquash x d a0 a1) = -- dim. of b,p,phi is x:d
  app d (app d p b0) b1                 -- d' should be x:d
  where fc w dir = res w (face (x:d) (x,dir))
        b0 = inhrec d (fc b Down) (fc p Down) (fc phi Down) a0
        b1 = inhrec d (fc b Up) (fc p Up) (fc phi Up) a1
--        d' = delete x d
inhrec _ b p phi (Kan ktype d (VInh a) box@(Box (Just (i,dir)) d' bc)) =
  kan ktype d b (mapBox irec box)
  where  irec (j, dir) v = inhrec (delete j d) (fc b) (fc p) (fc phi) v
           where fc v = res v (face d (j, dir))
--inhrec b p phi a = VInhRec b p phi a

kan :: KanType -> Dim -> Val -> VBox -> Val
kan Fill = fill
kan Com  = com

-- Kan filling
fill :: Dim -> Val -> VBox -> Val
fill d (VId a v0 v1) box =
--  trace ("Id fill box = " ++ show box ++ "\ntype a= " ++ show a ++ "\n"
--        ++ "v0 = " ++ show v0 ++ "\nv1 = " ++ show v1)
    Path $ fill (x:d) ax $ add2Sides (x,(v0,v1)) box'
  where x   = gensym d            -- i,d' <= d
        ax  = a `res` (deg d (x:d)) -- dim x:d
        box' = mapBox (\(j,_) v -> unPathAs (delete j d) x v) box
fill d (Ter (LSum nass) e) box@(Box (Just sb) db vb) =
-- assumes vb are constructor vals
--  trace ("fill sum")
  VCon name ws
  where
    as = case lookup name nass of
           Just as -> as
           Nothing -> error $ "fill: missing constructor "
                      ++ "in labelled sum " ++ name
    name = extractName (getSide box sb)
    extractName (VCon n _) = n
    extractName x = error "fill VLSum: not a constructor (bottom)"
    extractArgs = (\v -> case v of
                          VCon n xs | n == name -> xs
                          VCon n _ -> error $ "fill VLSum: constructors " ++ n ++
                               " and " ++ name ++ " do not match"
                          _ -> error "fill VLSum: not a constructor (side)")
    argboxes = listBox $ funMkBox (Just sb) db (extractArgs . getSide box)
    -- fill boxes for each argument position of the constructor
    ws = fills d as e argboxes
    err x = error $ "fill: not applied to constructor expressions " ++ show x
fill d (VEquivEq x d' a b f s t) box@(Box (Just sz@(z,dir)) dJ bc)
  | x /= z && x `notElem` dJ =
    -- d == x : d' ?!
    let ax0  = fill d' a (mapBox (\_ -> fstVal) box)
        bx0  = app d' f ax0
        bcx1 = mapBox (\_ vy -> sndVal vy `res` face d (x,Up)) box
--      bz   = mapBox (\_ vy -> sndVal vy) box
        bx1  = fill d' b bcx1
        v    = fill d (b `res` deg d' d) (add2Sides (x,(bx0,bx1)) box)
    in trace "VEquivEq case 1" $ VPair x ax0 v
  | x /= z && x `elem` dJ =
    let ax0 = getSide box (x,Down)
        -- TODO: Clean
        bz  = (`mapBox` box)
              (\(ny,dy) vy -> if x /= ny then sndVal vy else
                              if dy == Down then app d' f ax0 else vy)
        v   = fill d (b `res` deg d' d) bz
    in trace "VEquivEq case 2" $ VPair x ax0 v
  | x == z && dir == Down =
    let ax0 = getSide box (x,Down)
        bx0 = app d' f ax0
        v   = fill d (b `res` deg d' d) (mapBox mod box)
        mod sy v = if sy == sz then bx0 else sndVal v
    in trace "VEquivEq case 3" $ VPair x ax0 v
  | x == z && dir == Up =
    let y  = gensym d
        b  = getSide box sz
        sb = app d' s b
        gb = vfst sb
        abnd   = mapBox (\sy vy -> fst (vpairToSquare sy vy)) (boxBoundary box)
        bbnd   = mapBox (\sy vy -> snd (vpairToSquare sy vy)) (boxBoundary box)
        abox   = addSingleSide ((y,Down),gb) abnd
        afill  = fill (y:d') (a `res` deg d' (y : d')) abox
        acom   = com (y:d') (a `res` deg d' (y : d')) abox
        fafill = app (y : d') (f `res` deg d' (y : d')) afill
        sbsnd  = unPathAs d' x (vsnd sb)
        degb   = b `res` deg d' (y : d')

        bbox = addSingleSide ((y,Down),sbsnd)
               $ add2Sides (x,(fafill, degb)) bbnd

        bcom = com (y : d) (b `res` deg d' (y : d)) bbox

        vpairToSigma :: Name -> Val -> Val
        vpairToSigma z (VPair _ a0 v0) =
          VCon "pair" [a0, pathWith (delete z d') x v0]
        -- TODO: Permute name and dir
        vpairToSquare :: Side -> Val -> (Val,Val)
        vpairToSquare (z,dir) vp@(VPair _ a0 v0) =
          let t0   = t `res` face d' (z,dir)
              b0   = b `res` face d' (z,dir)
              d'z  = delete z d'
              VCon "pair" [l0,sq0] = -- in x : d'z
                unPathAs d'z x $ app d'z (app d'z t0 b0) (vpairToSigma z vp)
          in (vfst sq0, unPathAs (x:d'z) y $ vsnd sq0)

    in trace "VEquivEq case 4" $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"
fill d v box = Kan Fill d v box

-- is this sigma?
-- vsigma :: Val -> Val -> Val
-- vsigma a b =
--   Ter (LSum [("pair",[Var 1,App (Var 1) (Var 0)])]) (Pair (Pair Empty a) b)

-- vpair :: Val -> Val -> Val
-- vpair a b = VCon "pair" [a,b]

vfst, vsnd :: Val -> Val
vfst (VCon "pair" [a,b]) = a
vfst _ = error "vfst"
vsnd (VCon "pair" [a,b]) = b
vsnd _ = error "vsnd"

fills :: Dim -> [Ter] -> Env -> [VBox] -> [Val]
fills _ [] _ []              = []
fills d (a:as) e (box:boxes) = v : fills d as (Pair e v) boxes
  where v = fill d (eval d e a) box
fills _ _ _ _ = error "fills: different lengths of types and values"

-- Composition (ie., the face of fill which is created)
-- Note that the dimension is not the dimension of the output value,
-- but the one where the open box is specified
com :: Dim -> Val -> VBox -> Val
com d (VId a v0 v1) box@(Box (Just s) _ _) =
--  trace ("Id com box = " ++ show box ++ "\ntype a= " ++ show a ++ "\n"
--        ++ "v0 = " ++ show v0 ++ "\nv1 = " ++ show v1)
    res (fill d (VId a v0 v1) box) (face d s)
    -- face d i dir is (i=dir): d -> d-i
com d (Ter (LSum nass) e) box@(Box (Just s) _ _) =
  res (fill d (Ter (LSum nass) e) box) (face d s)
com d (VEquivEq x d' a b f s t) box@(Box (Just si) _ _) =
  fill d (VEquivEq x d' a b f s t) box `res` face d si

com d v box = Kan Com d v box


app :: Dim -> Val -> Val -> Val
app d (Ter (Lam t) e) u = eval d (Pair e u) t
app d (Kan Com bd (VPi a b) bcw@(Box (Just s@(i,dir)) d' _)) u =
       -- here: bd = i:d
--  trace ("Pi com box=" ++ show box ++ " \n" ++ "ufill " ++ show ufill)
    com bd (app bd b ufill) bcwu
  where ufill = fill bd a $ mkBox (Just (oppSide s, u)) []
        bcu = toOpenBox bd d' s ufill
        bcwu = appBox bd bcw bcu
app d (Kan Fill bd (VPi a b) bcw@(Box (Just s@(i,dir)) d' _)) v = -- here: bd = d
  trace ("Pi fill\n") com (x:d) (app (x:d) bx vfill) wvfills
  where x = gensym d            -- add a dimension
        ax = a `res` deg d (x:d)
        bx = b `res` deg d (x:d)
        di = delete i d         -- d minus i !!
        u = v `res` face d s
        ufill = fill d a $ mkBox (Just (oppSide s,u)) []
        -- cut an (i,d')-open box (in dir) from ufill
        bcu = toOpenBox bd d' s ufill
        ux = res u (deg di (x:di)) -- dim. x:(d-i)
        -- (i,[x])-open box in x:d (some choice on the order..) (mirror dir)
        vfill = fill (x:d) ax $ mkBox (Just (oppSide s,ux)) [(x,(ufill,v))]
        vbox = toOpenBox (x:d) d' s vfill
        bcwx = bcw `resBox` (deg d (x:d))
        wbox' = appBox (x:d) bcwx vbox
        wuimdir = getSide wbox' $ fromJust $ boxSingleSide wbox'
        wbnd  = boxBoundary wbox'
        -- the missing faces to get a (x, i:d')-open box in x:i:d (dir)
        wux0 = fill d (app d b ufill) (appBox d bcw bcu)
        wuidir = app (x:di) (com d (VPi a b) bcw) u `res` deg di (x:di)
        -- arrange the i-direction in the right order
        wuis = if dir == Up then (wuidir,wuimdir) else (wuimdir,wuidir)
        -- final open box in (app bx vsfill)
        wvfills = addSingleSide ((x,Up),wux0) $ add2Sides (i,(wuis)) wbnd
app d (VExt x d' bv fv gv pv) w = -- d = x:d'; values in vext have dim d'
  com (y:d) (app (y:d) bvxy wy) $ mkBox (Just ((y,Up),pvxw)) [(x,(left,right))]
  -- NB: there are various choices how to construct this
  where y = gensym d
        bvxy = bv `res` deg d' (y:d)
        wy = w `res` deg d (y:d)
        w0 = w `res` face d (x,Down)
        dg = deg d' (y:d')
        left = app d' fv w0 `res` dg -- y:d'
        wxtoy = rename d' w x y
        right = app (y:d') (gv `res` dg) wxtoy -- y:d'
        pvxw = unPathAs d' x $ app d' pv w0 -- x:d'
-- app d (VBranch alts e) (VCon name us) =
--   case lookup name alts of
--     Just t -> eval d (reverse us ++ e) t
--     Nothing -> error $ "app: VBranch with insufficient "
--                ++ "arguments; missing case for " ++ name
-- app d (VBranch nvs) (VCon name us) =
--   case lookup name nvs of
--     Just v -> apps d v us
--     Nothing -> error $ "app: VBranch with insufficient "
--                ++ "arguments; missing case for " ++ name
app d (Ter (Branch nvs) e) (VCon name us) =
  case lookup name nvs of
    Just t -> eval d (upds e us) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app d u v = VApp u v            -- error ?

apps :: Dim -> Val -> [Val] -> Val
apps d v []     = v
apps d v (u:us) = apps d (app d v u) us
-- TODO: rewrite as foldl(?r) (app d) v

-- TODO: QuickCheck!
prop_resId :: Val -> Mor -> Bool
prop_resId v f = res v (identity (cod f)) == v

-- TODO: express in haskell?
-- v is a cube in dimension dom f ==> res v f is a cube in dimension cod f

-- findName :: (Name -> Bool) -> Dim -> Maybe Name
-- findName _ [] = Nothing
-- findName f (x:xs) | f x = Just x
-- findName f (_:xs) | otherwise = findName f xs


res :: Val -> Mor -> Val
res VU _ = VU
res (VId v v0 v1) f = VId (res v f) (res v0 f) (res v1 f)
-- Cyril: because of this treatment of Path, res of deg cannot be identity!!
--        This could be fixed if Path embeds the dimensions as well.
res (Path v) f = Path $ res v (update f (gensym $ dom f) (gensym $ cod f))
res (VPi a b) f = VPi (res a f) (res b f)
-- res (Ter t e) f = eval (cod f) (mapEnv (`res` f) e) t
res (Ter t e) f = Ter t (mapEnv (`res` f) e) -- should be the same as above
res (VApp u v) f = app (cod f) (res u f) (res v f)
-- res (Res v g) f = res v (g `comp` f)
res (Kan Fill d u box@(Box (Just s@(i,dir)) d' _)) f
    | (f `ap` i) `direq` dir = getSide box s `res` (f `minus` i)
    | (f `ap` i) `direq` mirror dir = res (Kan Com d u box) (f `minus` i)
                                      -- This will be a Com
    | ndef f /= [] = let x:_        = ndef f
                         Left dirx  = f `ap` x
                     in getSide box (x, dirx) `res` (f `minus` x)
    | (i:d') `subset` def f =  fill (cod f) (u `res` f) (box `resBox` f)
  -- otherwise?
    | otherwise = error $ "Fill: not possible? box=" ++ show box
                           ++ "f = " ++ show f ++ " d= " ++ show d
res (Kan Com d u box@(Box (Just s@(i,dir)) d' _)) f
    | ndef f /= [] = let  x:_        = ndef f
                          Left dirx  = f `ap` x
                          g          = face d s `comp` f
                     in getSide box (x, dirx) `res` (g `minus` x)
    | d' `subset` def f = com co (u `res` fupd) (box `resBox` fupd)
    | otherwise = error $  "Com: not possible? box=" ++ show box
                          ++ "f = " ++ show f ++ " d= " ++ show d
    where co = cod f
          i' = gensym co
          fupd = update f i i'
-- res (Kan Com d u (BoxShape dir i d') bc) f = -- here: i:dom f = d
--   trace "res com" (res (res (fill d u (BoxShape dir i d') bc) g) ytodir)
--   where x = gensym d
--         co = cod f
--         y = gensym co
--         itox = update (identity (dom f)) i x -- (i=x):d->(d-i),x
--         fxtoy = update f x y -- (f,x=y):(d-i),x -> co,y
--         ytodir = face (y:co) y dir   -- (y=dir):co,y -> co
--         -- note that: (i=dir) f = (i=x) (f,x=y) (y=dir)
--         g = itox `comp` fxtoy   -- defined on x, hence non-circular call to res
--             -- g : d -> co, y has i in def g
res (VExt x d bv fv gv pv) f | x `elem` def f = -- dom f = x:d
  VExt (f `dap` x) d' (bv `res` fminusx) (fv `res` fminusx) (gv `res` fminusx)
       (pv `res` fminusx)
  where fminusx = f `minus` x
        d' = cod fminusx
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` Down = fv `res` (f `minus` x)
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` Up = gv `res` (f `minus` x)
res (VInh v) f = VInh (res v f)
res (VInc v) f = VInc (res v f)
res (VSquash x d u v) f | x `elem` def f = -- dom f = x:d
  VSquash (f `dap` x) d' (res u fminusx) (res v fminusx)
  where -- f-x : d -> d' ; f : x:d -> cod f;
        fminusx = f `minus` x
        d' = cod fminusx
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` Down = res u (f `minus` x)
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` Up = res v (f `minus` x)
res (VSquash x d u v) f = error $ "Vsquash impossible d= " ++ show d ++ " f = " ++ show f
--res (VInhRec b p phi a) f = inhrec (res b f) (res p f) (res phi f) (res a f)
--res (VBranch alts) f = VBranch $ map (\(n,v) -> (n,  res v f)) alts
res (VCon name vs) f = VCon name (map (`res` f) vs)
--res (VLSum nass) f = VLSum $ map (\(n,as) -> (n, map (`res` f) as)) nass

res (VEquivEq x d a b g s t) f | x `elem` def f =
  VEquivEq (f `dap` x) (cod f) (a `res` h) (b `res` h) (g `res` h)
           (s `res` h) (t `res` h)
   where h = f `minus` x
res (VEquivEq x d a b g s t) f | f `ap` x `direq` Down =
  a `res` (f `minus` x)
res (VEquivEq x d a b g s t) f | f `ap` x `direq` Up =
  b `res` (f `minus` x)
-- res (VEquivEq x d a b g s t) f = error "VEquivEq impossible"

res (VPair x a v) f | x `elem` def f =
  VPair (f `dap` x) (a `res` h) (v `res` f)
   where h = f `minus` x
res (VPair x a v) f | f `ap` x `direq` Down =
  a `res` (f `minus` x)
res (VPair x a v) f | f `ap` x `direq` Up =
  v `res` f

res p f = error $ "res: " ++ show p ++ " " ++ show f
  -- res v f = Res v f
--res _ _ = error "res: not possible?"


subset       :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (`elem` ys) xs

type VBox = Box Val

appBox :: Dim -> VBox -> VBox -> VBox
appBox d b0@(Box s0 d0 vs0) b1@(Box s1 d1 vs1) = Box s2 d2 vs2
    where s2     = if s0 == s1 then s0 else error msg_sf
          msg_sf = "appBox: incompatible single faces" ++ show (s0, s1)
          d2     = intersect d0 d1
          vs2    = [(s, app (delete x d) (getSide b0 s) (getSide b1 s))
                   | s@(x,dx) <- sides d2]

-- assumes s0 and d are in dom f
resBox :: VBox -> Mor -> VBox
resBox b@(Box s0 d vs) f = Box s0' d' vs' where
    s0' :: Maybe Side
    s0' = do (x, dx) <- s0
             case f `ap` x of
               Right fx -> return (fx, dx)
               Left  _  -> fail ""
    d' = rights [f `ap` x | x <- d]
    vs' = rights [(,v).(,dir) <$> f `ap` x | ((x,dir),v) <- vs]

toBox :: Dim -> Dim -> Val -> VBox
toBox d d' v = Box Nothing d' [(s, v `res` face d s) | s <- sides d']

toOpenBox :: Dim -> Dim -> Side -> Val -> VBox
toOpenBox d d' s = openBox s . toBox d d'
