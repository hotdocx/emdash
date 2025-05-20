-- Elaboration.hs

module Elaboration (check, infer) where

import Control.Exception
import Control.Monad
import Data.IORef

import qualified Data.IntMap as IM

import Common
import Cxt
import Errors
import Evaluation
import Metacontext
import Syntax
import Unification
import Value

import qualified Presyntax as P


-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t')

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act where
  go (t, va) = case force va of
    VPi x Impl a b -> do
      m <- freshMeta cxt
      let mv = eval (env cxt) m
      go (App t m Impl, b $$ mv)
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _), va) -> pure (t, va)
  (t               , va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act where
  go (t, va) = case force va of
    va@(VPi x Impl a b) -> do
      if x == name then
        pure (t, va)
      else do
        m <- freshMeta cxt
        let mv = eval (env cxt) m
        go (App t m Impl, b $$ mv)
    _ ->
      throwIO $ Error cxt $ NoNamedImplicitArg name

check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a

  -- If the icitness of the lambda matches the Pi type, check as usual
  (P.Lam x i t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') i -> do
    Lam x i' <$> check (bind cxt x a) t (b $$ VVar (lvl cxt))

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x Impl a b) -> do
    Lam x Impl <$> check (newBinder cxt x a) t (b $$ VVar (lvl cxt))

  (P.Let x a t u, a') -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x vt va) u a'
    pure (Let x a t u)

  (P.Hole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t

infer :: Cxt -> P.Tm -> IO (Tm, VTy)
infer cxt = \case
  P.SrcPos pos t ->
    infer (cxt {pos = pos}) t

  P.Var x -> do
    let go ix (types :> (x', origin, a))
          | x == x' && origin == Source = pure (Var ix, a)
          | otherwise                   = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)

  P.Lam x (Right i) t -> do
    a <- eval (env cxt) <$> freshMeta cxt
    let cxt' = bind cxt x a
    (t, b) <- insert cxt' $ infer cxt' t
    pure (Lam x i t, VPi x i a $ closeVal cxt b)

  P.Lam x Left{} t ->
    throwIO $ Error cxt $ InferNamedLam

  P.App t u i -> do

    -- choose implicit insertion
    (i, t, tty) <- case i of
      Left name -> do
        (t, tty) <- insertUntilName cxt name $ infer cxt t
        pure (Impl, t, tty)
      Right Impl -> do
        (t, tty) <- infer cxt t
        pure (Impl, t, tty)
      Right Expl -> do
        (t, tty) <- insert' cxt $ infer cxt t
        pure (Expl, t, tty)

    -- ensure that tty is Pi
    (a, b) <- case force tty of
      VPi x i' a b -> do
        unless (i == i') $
          throwIO $ Error cxt $ IcitMismatch i i'
        pure (a, b)
      tty -> do
        a <- eval (env cxt) <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt tty (VPi "x" i a b)
        pure (a, b)

    u <- check cxt u a
    pure (App t u i, b $$ eval (env cxt) u)

  P.U ->
    pure (U, VU)

  P.Pi x i a b -> do
    a <- check cxt a VU
    b <- check (bind cxt x (eval (env cxt) a)) b VU
    pure (Pi x i a b, VU)

  P.Let x a t u -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x vt va) u
    pure (Let x a t u, b)

  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)

--- Unification.hs

module Unification (unify) where

import Control.Exception
import Data.IORef

import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value

-- Unification
--------------------------------------------------------------------------------

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl             -- ^ size of Γ
  , cod :: Lvl             -- ^ size of Δ
  , ren :: IM.IntMap Lvl}  -- ^ mapping from Δ vars to Γ vars

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

-- | @invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []             = pure (0, mempty)
      go (sp :> (t, _)) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []             = pure t
  goSp pren t (sp :> (u, i)) = App <$> goSp pren t sp <*> go pren u <*> pure i

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x i t  -> Lam x i <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x i a b -> Pi x i <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VU          -> pure U

-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [Icit] -> Tm -> Tm
lams = go (0 :: Int) where
  go x []     t = t
  go x (i:is) t = Lam ("x"++show (x+1)) i $ go (x + 1) is t

--       Γ      ?α         sp       rhs
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (reverse $ map snd sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
-- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp l sp sp' >> unify l t t'

  _                              -> throwIO UnifyError -- rigid mismatch error

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp'

  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError  -- rigid mismatch error

---

module Main where

import Control.Exception
import System.Environment
import System.Exit

import Common
import Cxt
import Errors
import Evaluation
import Metacontext
import Parser
import Pretty
import Elaboration

import qualified Presyntax as P

--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-implicit-args [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw = do

  let elab = do
        (t, file) <- getRaw
        infer (emptyCxt (initialPos file)) t
          `catch` \e -> displayError file e >> exitSuccess

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ nf [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ["type"] -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, a) <- elab
      displayMetas
      putStrLn $ showTm0 t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

--- Errors.hs

module Errors where

import Control.Exception
import Text.Printf

import Common
import Cxt
import Syntax

--------------------------------------------------------------------------------

data UnifyError = UnifyError
  deriving (Show, Exception)

data ElabError
  = NameNotInScope Name
  | CantUnify Tm Tm
  | InferNamedLam
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  deriving (Show, Exception)

data Error = Error Cxt ElabError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error cxt e) = do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t'   ->
          ("Cannot unify expected type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with inferred type\n\n" ++
           "  " ++ showTm cxt t')
        InferNamedLam ->
          "Cannot infer type for lambda with named argument"
        NoNamedImplicitArg name ->
          "No named implicit argument with name " ++ name
        IcitMismatch i i' -> printf (
          "Function icitness mismatch: expected %s, got %s.")
          (show i) (show i')

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

--- Metacontext.hs


module Metacontext where

import Data.IORef
import System.IO.Unsafe

import qualified Data.IntMap as IM

import Common
import Value

--------------------------------------------------------------------------------

data MetaEntry = Solved Val | Unsolved

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

-- Pretty.hs

module Pretty (prettyTm, showTm0, displayMetas) where

import Control.Monad
import Data.IORef
import Text.Printf

import qualified Data.IntMap.Strict as IM

import Common
import Evaluation
import Metacontext
import Syntax

--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  bracket :: ShowS -> ShowS
  bracket ss = ('{':).ss.('}':)

  piBind ns x Expl a = showParen True ((x++) . (" : "++) . go letp ns a)
  piBind ns x Impl a = bracket        ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = bracket (x++)
  lamBind x Expl = (x++)

  goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
  goBDS p ns m bds = case (ns, bds) of
    ([]      , []             ) -> (("?"++show m)++)
    (ns :> n , bds :> Bound   ) -> par p appp $ goBDS appp ns m bds . (' ':) . (n++)
    (ns :> n , bds :> Defined ) -> goBDS appp ns m bds
    _                           -> error "impossible"

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u Expl              -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl              -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (fresh ns -> x) i t   -> par p letp $ ("λ "++) . lamBind x i . goLam (ns:>x) t where
                                   goLam ns (Lam (fresh ns -> x) i t) =
                                     (' ':) . lamBind x i . goLam (ns:>x) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" Expl a b           -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) i a b  -> par p pip $ piBind ns x i a . goPi (ns:>x) b where
                                   goPi ns (Pi (fresh ns -> x) i a b)
                                     | x /= "_" = piBind ns x i a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m bds        -> goBDS p ns m bds

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved -> printf "let ?%s = ?;\n" (show m)
    Solved v -> printf "let ?%s = %s;\n" (show m) (showTm0 $ quote 0 v)
  putStrLn ""

--- Evaluation.hs

module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp) where

import Common
import Metacontext
import Syntax
import Value

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Icit -> Val
vApp t ~u i = case t of
  VLam _ _ t  -> t $$ u
  VFlex  m sp -> VFlex m  (sp :> (u, i))
  VRigid x sp -> VRigid x (sp :> (u, i))
  _           -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []           -> t
  sp :> (u, i) -> vApp (vAppSp t sp) u i

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vApp (vAppBDs env v bds) t Expl
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"

eval :: Env -> Tm -> Val
eval env = \case
  Var x              -> env !! unIx x
  App t u i          -> vApp (eval env t) (eval env u) i
  Lam x i t          -> VLam x i (Closure env t)
  Pi x i a b         -> VPi x i (eval env a) (Closure env b)
  Let _ _ t u        -> eval (env :> eval env t) u
  U                  -> VU
  Meta m             -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds

force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp l t sp) (quote l u) i

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x i t  -> Lam x i (quote (l + 1) (t $$ VVar l))
  VPi x i a b -> Pi x i (quote l a) (quote (l + 1) (b $$ VVar l))
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

-- Common.hs


module Common (
    module Common
  , SourcePos(..)
  , Pos
  , unPos
  , initialPos) where

import Text.Megaparsec

type Name = String

data Icit = Impl | Expl deriving (Eq)
data BD = Bound | Defined deriving Show

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}

--- Cxt.hs

module Cxt where

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving Eq
type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt {           -- used for:
                           -----------------------------------
    env   :: Env           -- evaluation
  , lvl   :: Lvl           -- unification
  , types :: Types         -- raw name lookup, pretty printing
  , bds   :: [BD]          -- fresh meta creation
  , pos   :: SourcePos     -- error reporting
  }

cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _) -> x) . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Source, a)) (bds :> Bound) pos

-- | Insert a new binding.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Inserted, a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, Source, a)) (bds :> Defined) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)


--- Presyntax.hs

module Presyntax where

import Common

data Tm
  = Var Name                       -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit)   -- t u  | t {u} | t {x = u}
  | U                              -- U
  | Pi Name Icit Tm Tm             -- (x : A) -> B | {x : A} -> B
  | Let Name Tm Tm Tm              -- let x : A = t; u
  | SrcPos SourcePos Tm            -- source position for error reporting
  | Hole                           -- _
  deriving Show


--- Value.hs

module Value where

import Common
import Syntax

type Env     = [Val]
type Spine   = [(Val, Icit)]
data Closure = Closure Env Tm
type VTy     = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VTy {-# unpack #-} Closure
  | VU

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []

--- Syntax.hs


module Syntax where

import Common

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]
  deriving Show

--- Unification.hs
module Unification (unify) where

import Control.Exception
import Data.IORef

import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value

-- Unification
--------------------------------------------------------------------------------

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl             -- ^ size of Γ
  , cod :: Lvl             -- ^ size of Δ
  , ren :: IM.IntMap Lvl}  -- ^ mapping from Δ vars to Γ vars

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

-- | @invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []             = pure (0, mempty)
      go (sp :> (t, _)) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []             = pure t
  goSp pren t (sp :> (u, i)) = App <$> goSp pren t sp <*> go pren u <*> pure i

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x i t  -> Lam x i <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x i a b -> Pi x i <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VU          -> pure U

-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [Icit] -> Tm -> Tm
lams = go (0 :: Int) where
  go x []     t = t
  go x (i:is) t = Lam ("x"++show (x+1)) i $ go (x + 1) is t

--       Γ      ?α         sp       rhs
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (reverse $ map snd sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
-- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp l sp sp' >> unify l t t'

  _                              -> throwIO UnifyError -- rigid mismatch error

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp'

  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError  -- rigid mismatch error


-- example.txt



-- bracketed args are implicit, elaboration inserts implicit lambdas for them (if they're not
-- already present)
let id : {A : U} -> A -> A = \x. x;   -- elaborated to \{A} x. x

-- implicit arg types can be omitted
let const : {A B} -> A -> B -> A = \x y. x;

-- function arguments can be grouped:
let group1 : {A B : U}(x y z : A) -> B -> B = \x y z b. b;
let group2 : {A B}(x y z : A) -> B -> B = \x y z b. b;

-- explicit id function used for annotation as in Idris
let the : (A : _) -> A -> A = \_ x. x;

-- implicit args can be explicitly given
let argTest1 = const {U}{U} U;

-- or can be given by name (names come from the function types)
let argTest2 = const {B = U} U;  -- only give B, the second implicit arg

-- likewise, implicit lambdas can be explicitly given
let id2 : {A} -> A -> A = \{A} x. x;

-- we can also bind only some implicit args, using named implicit lambdas
let namedLam  : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a; -- second arg in scope as B
let namedLam2 : {A B C} -> A -> B -> C -> A = \{B = X} a b c. a; -- second arg in scope as X
let namedLam2 : {A B C} -> A -> B -> C -> A = \{C = X} a b c. a; -- third arg in scope as X

{-
Implicit application insertion rules:

  - In "t u", if t has type {x : A} -> B, we insert a fresh application as t {?a} u
  - In "t {x = u}", we insert applications until we hit the "x" domain name. if t's type
    has no such domain binder name, it's an error.
  - In "t {u}", we do not insert applications
  - Otherwise, given t,
    - if t = \{x}. t, we don't insert
    - otherwise if t has type {x : A} -> B, we insert a fresh application

Implicit lambda insertion rules:

  - We check t with {x : A} -> B
    - if t is an implicit lambda or a named implicit lambda with name=x, we don't insert
    - otherwise, we insert \{x}
-}

-- Here the output rhs is \{A}. id {A}. First, we insert \{A}, then we apply id to {?n},
-- and ?n is solved to A a bit later.
let insert : {A} -> A -> A = id;

-- Here we don't insert, because rhs is already an implicit lambda.
let noinsert = \{A} x. the A x;

-- Here we insert, because although we already have an implicit lambda, it is applied
-- explicitly to something.
let insert2 = (\{A} x. the A x) U;  -- (\{A} x. the A x) {U} U


--------------------------------------------------------------------------------

-- bool
let Bool : U
    = (B : _) -> B -> B -> B;
let true : Bool
    = \B t f. t;
let false : Bool
    = \B t f. f;
let not : Bool -> Bool
    = \b B t f. b B f t;

-- lists
let List : U -> U
    = \A. (L : _) -> (A -> L -> L) -> L -> L;
let nil : {A} -> List A
    = \L cons nil. nil;
let cons : {A} -> A -> List A -> List A
    = \x xs L cons nil. cons x (xs L cons nil);
let map : {A B} -> (A -> B) -> List A -> List B
    = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
let list1 : List Bool
    = cons true (cons false (cons true nil));

-- dependent function composition
let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
           (f : {a}(b : B a) -> C b)
           (g : (a : A) -> B a)
           (a : A)
           -> C (g a)
    = \f g a. f (g a);

let compExample = comp (cons true) (cons false) nil;

-- nat
let Nat : U
    = (N : U) -> (N -> N) -> N -> N;
let mul : Nat -> Nat -> Nat
    = \a b N s z. a _ (b _ s) z;
let ten : Nat
    = \N s z. s (s (s (s (s (s (s (s (s (s z)))))))));
let hundred = mul ten ten;

-- Leibniz equality
let Eq : {A} -> A -> A -> U
    = \{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A}{x : A} -> Eq x x
    = \_ px. px;

let sym : {A x y} → Eq {A} x y → Eq y x
  = λ {A}{x}{y} p. p (λ y. Eq y x) refl;

the (Eq (mul ten ten) hundred) refl