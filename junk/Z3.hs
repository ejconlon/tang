module Tang.Z3
  ( solveZ3
  , checkZ3
  )
where

import Control.Monad.State.Strict (MonadIO, MonadState (..), StateT (..), lift)
import Data.Foldable (toList)
import Data.Functor.Foldable (cata)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Tang.PropDef
  ( Assignment (..)
  , Clause (..)
  , Conjunction (..)
  , DProp
  , DPropF (..)
  , Polarity (..)
  , Var (Var)
  , VarConjunction (..)
  )
import Tang.Solver (Checker, ModelResult (..), Result (..), Solver)
import Tang.VarEnv (VarId (..))
import Z3.Monad (AST, MonadZ3 (..), Z3)
import Z3.Monad qualified as Z3

type ZMap v = Map v AST

newtype Z v a = Z {unZ :: StateT (ZMap v) Z3 a}
  deriving newtype (Functor, Applicative, Monad, MonadState (ZMap v), MonadIO)

runZ :: Z v a -> ZMap v -> IO (a, ZMap v)
runZ z m = Z3.evalZ3 (runStateT (unZ z) m)

evalZ :: Z v a -> IO a
evalZ = fmap fst . flip runZ Map.empty

instance MonadZ3 (Z v) where
  getSolver = Z (lift getSolver)
  getContext = Z (lift getContext)

class Ingestible v f | f -> v where
  ingest :: f v -> Z v AST

instance Ingestible Text DProp where
  ingest = cata go
   where
    go = \case
      DPropVarF v -> do
        m <- get
        case Map.lookup v m of
          Just a -> pure a
          Nothing -> do
            s <- Z3.mkStringSymbol (T.unpack v)
            a <- Z3.mkBoolVar s
            put (Map.insert v a m)
            pure a
      DPropBoolF b -> Z3.mkBool b
      DPropNotF sx -> do
        x <- sx
        Z3.mkNot x
      DPropAndF sx sy -> do
        x <- sx
        y <- sy
        Z3.mkAnd [x, y]
      DPropOrF sx sy -> do
        x <- sx
        y <- sy
        Z3.mkOr [x, y]

instance Ingestible VarId VarConjunction where
  ingest = go1
   where
    go1 (VarConjunction (Conjunction cls)) = do
      xs <- traverse go2 (toList cls)
      Z3.mkAnd xs
    go2 (Clause vs) = do
      ys <- traverse go3 (toList vs)
      Z3.mkOr (toList ys)
    go3 (Var pol nm) = do
      m <- get
      z <- case Map.lookup nm m of
        Just a -> pure a
        Nothing -> do
          s <- Z3.mkIntSymbol (unVarId nm)
          a <- Z3.mkBoolVar s
          put (Map.insert nm a m)
          pure a
      case pol of
        PolarityPos -> pure z
        PolarityNeg -> Z3.mkNot z

traverseMap :: (Applicative m) => Map a b -> (b -> m (Maybe c)) -> m (Map a c)
traverseMap m f = Map.traverseMaybeWithKey (const f) m

assertAndSolve :: AST -> Z v (ModelResult (Assignment v))
assertAndSolve ast = do
  Z3.assert ast
  (res, mmodel) <- Z3.getModel
  case res of
    Z3.Sat ->
      case mmodel of
        Nothing -> error "impossible"
        Just model -> do
          kas <- get
          let eval = Z3.evalBool model
          kbs <- traverseMap kas eval
          pure (ModelResultSat (Assignment kbs))
    _ -> pure ModelResultUnsat

assertAndCheck :: AST -> Z v Result
assertAndCheck ast = do
  Z3.assert ast
  res <- Z3.check
  case res of
    Z3.Sat -> pure ResultSat
    _ -> pure ResultUnsat

solveZ3 :: (Ingestible v f) => Solver f v v
solveZ3 s = evalZ (ingest s >>= assertAndSolve)

checkZ3 :: (Ingestible v f) => Checker f v
checkZ3 s = evalZ (ingest s >>= assertAndCheck)
