module Eval where

import Control.Arrow hiding (app)
import Data.Either
import Data.List
import Data.Maybe

import Debug.Trace

import Core

type Name = Integer
type Dim  = [Name]
data Dir  = Up | Down deriving (Eq, Show)

mirror :: Dir -> Dir
mirror Up = Down
mirror Down = Up

gensym :: Dim -> Name
gensym [] = 0
gensym xs = maximum xs + 1

gensyms :: Dim -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

-- The pair of values is (down,up)
data Box a = Box Dir Name a [(Name,(a,a))]
  deriving (Eq,Show)

mapBox :: (a -> b) -> Box a -> Box b
mapBox f (Box d n x xs) = Box d n (f x) [ (n',(f down,f up))
                                        | (n',(down,up)) <- xs ]

-- assumes name appears as non principal a direction of the box
lookBox :: Box a -> Name -> Dir -> a
lookBox (Box _ _ _ nvs) x dir = case lookup x nvs of
  Just (down,up) | dir == Up -> up
                 | otherwise -> down
  Nothing -> error $ "lookBox: box not defined on " ++ show x ++ " " ++ show dir

nonPrincipal :: Box a -> [Name]
nonPrincipal (Box _ _ _ nvs) = map fst nvs

instance Functor Box where fmap = mapBox

data KanType = Fill | Com deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VId Val Val Val
         | Path Name Val             -- tag values which are paths
         | VExt Name Val Val Val Val -- has dimension (name:dim);
                                         -- vals of dimension dim
         | VPi Val Val
         | VInh Val
         | VInc Val
         | VSquash Name Val Val  -- has dimension (name:dim); vals
                                     -- of dimension dim
         | VCon Ident [Val]
         | Kan KanType Val (Box Val)
         | VEquivEq Name Val Val Val Val Val -- of type U of dimension name:dim
           -- VEquivEq x d a b f s t where
         | VPair Name Val Val -- of type VEquiv
  deriving (Show, Eq)

fstVal, sndVal :: Val -> Val
fstVal (VPair _ a _) = a
fstVal x             = error $ "fstVal: " ++ show x
sndVal (VPair _ _ v) = v
sndVal x             = error $ "fstVal: " ++ show x

data Env = Empty
         | Pair Env Val
         | PDef [Ter] Env
  deriving (Eq,Show)

upds :: Env -> [Val] -> Env
upds = foldl Pair

look :: Int -> Env -> Val
look 0 (Pair _ u)     = u
look k (Pair s _)     = look (k-1) s
look k r@(PDef es r1) = look k (upds r1 (evals r es))

ter :: Ter -> Env -> Val
ter t e = eval e t

evals :: Env -> [Ter] -> [Val]
evals e = map (eval e)

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty = Empty
mapEnv f (Pair e v) = Pair (mapEnv f e) (f v)
mapEnv f (PDef ts e) = PDef ts (mapEnv f e)

faceEnv :: Env -> Name -> Dir -> Env
faceEnv e x dir = mapEnv (\u -> face u x dir) e

-- Compute the face map.
-- (i=b) : d -> d-i
face :: Val -> Name -> Dir -> Val
face u x dir =
  let fc v = face v x dir in case u of
  VU          -> VU
  Ter t e     -> ter t (faceEnv e x dir)
  VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
  Path y v | x == y    -> u
           | otherwise -> Path y (fc v)
  VExt y b f g p | x == y && dir == Down -> f
                 | x == y && dir == Up   -> g
                 | otherwise             -> VExt y (fc b) (fc f) (fc g) (fc p)
  VPi a f    -> VPi (fc a) (fc f)
  VInh v     -> VInh (fc v)
  VInc v     -> VInc (fc v)
  VSquash y v0 v1 | x == y && dir == Down -> v0
                  | x == y && dir == Up   -> v1
                  | otherwise             -> VSquash y (fc v0) (fc v1)
  VCon c us -> VCon c (map fc us)
  VEquivEq y a b f s t | x == y && dir == Down -> a
                       | x == y && dir == Up   -> b
                       | otherwise             -> VEquivEq y (fc a) (fc b) (fc f) (fc s) (fc t)
  VPair y a v | x == y && dir == Down -> a
              | x == y && dir == Up   -> fc v
              | otherwise             -> VPair y (fc a) (fc v)
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox b x dir
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b    -> face (lookBox b x dir) y dir'



unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

-- test that names only occur once in support
support :: Val -> [Name]
support VU                = []
support (Ter _ e)         = supportEnv e
support (VId a v0 v1)     = unionsMap support [a,v0,v1]
support (Path x v)        = delete x $ support v
support (VInh v)          = support v
support (VInc v)          = support v
support (VPi v1 v2)       = unionsMap support [v1,v2]
support (VCon _ vs)       = unionsMap support vs
support (VSquash x v0 v1) = [x] `union` unionsMap support [v0,v1]
support (VExt x b f g p)  = [x] `union` unionsMap support [b,f,g,p]
support (Kan Fill a box)  = support a `union` supportBox box
support (Kan Com a box@(Box _ n _ _)) =
  delete n (support a `union` supportBox box)
support (VEquivEq x a b f s t) = [x] `union` unionsMap support [a,b,f,s,t]
support (VPair x a v)          = [x] `union` unionsMap support [a,v]

supportBox :: Box Val -> [Name]
supportBox (Box dir n v vns) = [n] `union` support v `union`
  unions [ [y] `union` unionsMap support [v1,v2] | (y,(v1,v2)) <- vns ]

supportEnv :: Env -> [Name]
supportEnv Empty      = []
supportEnv (Pair e v) = supportEnv e `union` support v
supportEnv (PDef _ e) = supportEnv e

-- TODO: Typeclass for freshness!
fresh :: Val -> Name
fresh = gensym . support

freshEnv :: Env -> Name
freshEnv = gensym . supportEnv

swapName :: Name -> Name -> Name -> Name
swapName z x y | z == x    = y
               | z == y    = x
               | otherwise = z

swapEnv :: Env -> Name -> Name -> Env
swapEnv e x y = mapEnv (\u -> swap u x y) e

swap :: Val -> Name -> Name -> Val
swap u x y =
  let sw u = swap u x y in case u of
  VU      -> VU
  Ter t e -> Ter t (swapEnv e x y)
  VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
  Path z v | z /= x && z /= y    -> Path z (sw v)
           | otherwise -> let z' = gensym ([x] `union` [y] `union` support v)
                              v' = swap v z z'
                          in Path z' (sw v')
  VExt z b f g p -> VExt (swapName z x y) (sw b) (sw f) (sw g) (sw p)
  VPi a f -> VPi (sw a) (sw f)
  VInh v -> VInh (sw v)
  VInc v -> VInc (sw v)
  VSquash z v0 v1 -> VSquash (swapName z x y) (sw v0) (sw v1)
  VCon c us -> VCon c (map sw us)
  VEquivEq z a b f s t -> VEquivEq (swapName z x y) (sw a) (sw b) (sw f) (sw s) (sw t)
  VPair z a v -> VPair (swapName z x y) (sw a) (sw v)
  Kan Fill a b@(Box dir' z v nvs) ->
    fill (sw a) (Box dir' (swapName z x y) (sw v)
                 [ (swapName n x y,(sw v0,sw v1)) | (n,(v0,v1)) <- nvs ])
  Kan Com a b@(Box dir' z v nvs)
    | z /= x && z /= y    -> com (sw a) (Box dir' (swapName z x y) (sw v)
                                         [ (swapName n x y,(sw v0,sw v1)) | (n,(v0,v1)) <- nvs ])
    | otherwise -> let z' = gensym ([x] `union` [y] `union` support u)
                       a' = swap a z z'
                       v' = swap v z z'
                       nvs' = [ (swapName n z z',(swap v0 z z',swap v1 z z'))
                              | (n,(v0,v1)) <- nvs ]
                   in sw (Kan Com a' (Box dir' z' v' nvs'))

appName :: Val -> Name -> Val
appName (Path x u) y = swap u x y
appName v _          = error $ "appName: should be a path: " ++ show v

eval :: Env -> Ter -> Val
eval _ U             = VU
eval e (Var i)       = look i e
eval e (Id a a0 a1)  = VId (eval e a) (eval e a0) (eval e a1)
eval e (Refl a)      = Path (freshEnv e) $ eval e a
eval e (Trans c p t) = com (app (eval e c) pv) box
  where x   = freshEnv e
        pv  = appName (eval e p) x
        box = Box Up x (eval e t) []
eval e (TransInv c p t) = com (app (eval e c) pv) box
  where x   = freshEnv e
        pv  = appName (eval e p) x
        box = Box Down x (eval e t) []
-- TODO: throw out _, not needed?
eval e (J a u c w _ p) = com (app (app cv omega) sigma) box
  where
    se    = supportEnv e
    x:y:_ = gensyms se
    uv    = eval e u
    pv    = appName (eval e p) x
    theta = fill (eval e a) (Box Up x uv [(y,(uv,pv))])
    sigma = Path x theta
    omega = face theta x Up
    cv    = eval e c
    box   = Box Up y (eval e w) []
eval e (JEq a u c w) = Path y $ fill (app (app cv omega) sigma) box
  where
    se    = supportEnv e
    x:y:_ = gensyms se
    uv    = eval e u
    theta = fill (eval e a) (Box Up x uv [(y,(uv,uv))])
    sigma = Path x theta
    omega = face theta x Up
    cv    = eval e c
    box   = Box Up y (eval e w) []
eval e (Ext b f g p) = Path x $ VExt x (eval e b) (eval e f) (eval e g) (eval e p)
  where x = freshEnv e
eval e (Pi a b)      = VPi (eval e a) (eval e b)
eval e (Lam t)       = Ter (Lam t) e -- stop at lambdas
eval e (App r s)     = app (eval e r) (eval e s)
eval e (Inh a)       = VInh (eval e a)
eval e (Inc t)       = VInc (eval e t)
eval e (Squash r s)  = Path x $ VSquash x (eval e r) (eval e s)
  where x = freshEnv e
eval e (InhRec b p phi a)  = inhrec (eval e b) (eval e p) (eval e phi) (eval e a)
eval e (Where t def)       = eval (PDef def e) t
eval e (Con name ts)       = VCon name (map (eval e) ts)
eval e (Branch alts)       = Ter (Branch alts) e
eval e (LSum ntss)         = Ter (LSum ntss) e
eval e (EquivEq a b f s t) =  -- TODO: are the dimensions of a,b,f,s,t okay?
  Path x $ VEquivEq x (eval e a) (eval e b) (eval e f) (eval e s) (eval e t)
    where x = freshEnv e

modBox :: (Dir -> Name -> a -> a) -> Box a -> Box a
modBox f (Box dir x v nvs) =
  Box dir x (f dir x v) [ (n,(f Down n v0,f Up n v1)) | (n,(v0,v1)) <- nvs ]

inhrec :: Val -> Val -> Val -> Val -> Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) = appName (app (app p b0) b1) x
  where fc w = w `face` x
        b0   = inhrec (fc b Down) (fc p Down) (fc phi Down) a0
        b1   = inhrec (fc b Up)   (fc p Up)   (fc phi Up)   a1
inhrec b p phi (Kan ktype (VInh a) box@(Box dir x v nvs)) =
  kan ktype b (modBox irec box)
    where irec dir j v = let fc v = face v j dir
                         in inhrec (fc b) (fc p) (fc phi) v
-- inhrec b p phi a = VInhRec b p phi a

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

-- TODO: Clean
transposeBox :: Box [Val] -> [Box Val]
transposeBox b@(Box dir _ [] _)      = []
transposeBox (Box dir x (v:vs) nvss) =
  Box dir x v [ (n,(head vs0,head vs1)) | (n,(vs0,vs1)) <- nvss ] :
  transposeBox (Box dir x vs [ (n,(tail vs0,tail vs1))
                             | (n,(vs0,vs1)) <- nvss ])

consBox :: (Name,(a,a)) -> Box a -> Box a
consBox nv (Box dir x v nvs) = Box dir x v (nv : nvs)

-- Kan filling
fill :: Val -> Box Val -> Val
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = Path x $ fill a box'
  where x    = gensym (support vid `union` supportBox box)
        box' = mapBox (`appName` x) box
-- assumes cvs are constructor vals
fill (Ter (LSum nass) e) box@(Box _ _ (VCon n _) _) = VCon n ws
  where as = case lookup n nass of
               Just as -> as
               Nothing -> error $ "fill: missing constructor "
                       ++ "in labelled sum " ++ n
        boxes :: [Box Val]
        boxes = transposeBox $ mapBox unCon box
        -- fill boxes for each argument position of the constructor
        ws    = fills as e boxes
-- a and b should be independent of x
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    -- d == x : d' ?!
    let ax0  = fill a (mapBox fstVal box)
        bx0  = app f ax0
        bx   = mapBox sndVal box
        bcx1 = mapBox (\u -> face u x Up) bx
        bx1  = fill b bcx1
        v    = fill b ((x,(bx0,bx1)) `consBox` bx)
    in trace "VEquivEq case 1" $ VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box =
    let ax0 = lookBox box x Down
        bx  = modBox (\dy ny vy -> if x /= ny then sndVal vy else
                                      if dy == Down then app f ax0 else vy) box
        v   = fill b bx
    in trace "VEquivEq case 2" $ VPair x ax0 v
  | x == z && dir == Up =
    let ax0  = vz
        bx0  = app f ax0
        nvs' = [ (n,(sndVal v0,sndVal v1)) | (n,(v0,v1)) <- nvs ]
        v    = fill b (Box dir z bx0 nvs')
    in trace "VEquivEq case 3" $ VPair x ax0 v
  | x == z && dir == Down =
     let y  = gensym (support veq `union` supportBox box)
         b  = vz
         sb = app s b
         gb = vfst sb
         vy = appName (vsnd sb) x

         vpTSq :: Dir -> Name -> Val -> (Val,Val)
         vpTSq dz nz (VPair z a0 v0) =
             let vp = VCon "pair" [a0, Path z v0]
                 t0 = face t nz dz
                 b0 = face b nz dz
                 VCon "pair" [l0,sq0] = appName (app (app t0 b0) vp) y
             in (l0,appName sq0 x)  -- TODO: check the correctness of the square s0

         -- TODO: Use modBox!
         vsqs   = [ (n,(vpTSq Down n v0,vpTSq Up n v1)) | (n,(v0,v1)) <- nvs]
         afill  = fill a (Box Up y gb [ (n,(d0,d1))
                                      | (n,((d0,_),(d1,_))) <- vsqs ])
         acom   = face afill y Up
         fafill = app f afill
         bcom   = com b (Box Up y vy ((x, (fafill,b)) :
                              [ (n,(u0,u1)) | (n,((_,u0),(_,u1))) <- vsqs ]))
     in trace "VEquivEq case 4" $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"
fill v b = Kan Fill v b

-- Given C : B -> U such that s : (x : B) -> C x and
-- t : (x : B) (y : C x) -> Id (C x) (s x) y, we construct
-- a filling of closed empty cube (i.e., the boundary
-- of a cube) over a cube u in B.
-- C b = sigma (a : A) (Id B (f a) b)

vfst, vsnd :: Val -> Val
vfst (VCon "pair" [a,b]) = a
vfst _                   = error "vfst"
vsnd (VCon "pair" [a,b]) = b
vsnd _                   = error "vsnd"

fills :: [Ter] -> Env -> [Box Val] -> [Val]
fills [] _ []              = []
fills (a:as) e (box:boxes) = v : fills as (Pair e v) boxes
  where v = fill (eval e a) box
fills _ _ _ = error "fills: different lengths of types and values"

-- Composition (ie., the face of fill which is created)
-- Note that the dimension is not the dimension of the output value,
-- but the one where the open box is specified
com :: Val -> Box Val -> Val
com vid@VId{} box@(Box dir i _ _)      = face (fill vid box) i dir
com ter@Ter{} box@(Box dir i _ _)      = face (fill ter box) i dir
com veq@VEquivEq{} box@(Box dir i _ _) = face (fill veq box) i dir
com v box                              = Kan Com v box

cubeToBox :: Val -> Box () -> Box Val
cubeToBox v (Box dir x () nvs) =
  Box dir x (face v x dir) [ (n,(face v n Down,face v n Up)) | (n,_) <- nvs ]

shapeOfBox :: Box a -> Box ()
shapeOfBox = mapBox (const ())

-- Maybe generalize?
appBox :: Box Val -> Box Val -> Box Val
appBox (Box dir x v nvs) (Box _ _ u nus) = Box dir x (app v u) nvus
  where nvus = [ let Just (u0,u1) = lookup n nus in (n,(app v0 u0,app v1 u1))
               | (n,(v0,v1)) <- nvs ]

app :: Val -> Val -> Val
app (Ter (Lam t) e) u                           = eval (Pair e u) t
app (Kan Com (VPi a b) box@(Box dir x v nvs)) u = com (app b ufill) (appBox box bcu)
  where ufill = fill a (Box (mirror dir) x u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v =
  trace ("Pi fill\n") $ com (app b vfill) (Box Up x vx ((i,(vi0,vi1)):nvs))
  where x     = gensym (support kf `union` support v)
        u     = face v i dir
        ufill = fill a (Box (mirror dir) i u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
        vfill = fill a (Box (mirror dir) i u [(x,(ufill,v))])
        vx    = fill (app b ufill) (appBox box bcu)
        vi0   = app w (face vfill i Down)
        vi1   = com (app b ufill) (appBox box bcu)
        nvs   = [ (n,(app ws0 (face vfill n Down),app ws1 (face vfill n Up)))
                | (n,(ws0,ws1)) <- nws]
app vext@(VExt x bv fv gv pv) w = com (app bv w) (Box Up y pvxw [(x,(left,right))])
  -- NB: there are various choices how to construct this
  where y     = gensym (support vext `union` support w)
        w0    = face w x Down
        left  = app fv w0
        right = app gv (swap w x y)
        pvxw  = appName (app pv w0) x
app (Ter (Branch nvs) e) (VCon name us) = case lookup name nvs of
    Just t  -> eval (upds e us) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app _ _ = error "app"
