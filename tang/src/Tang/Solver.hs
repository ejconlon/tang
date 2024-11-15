{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Tang.Solver where

import Control.Exception (Exception, throwIO)
import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), ask, asks)
import Control.Monad.State.Strict (MonadState (..), gets)
import Data.Foldable (for_)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.String (IsString (..))
import Data.Tuple (swap)
import Tang.Exp (Exp (..), ExpF (..))
import Z3.Base qualified as ZB
import Z3.Monad qualified as Z
import Z3.Opts qualified as ZO

type Params = Map String PVal

data PVal
  = PVBool !Bool
  | PVWord !Word
  | PVDouble !Double
  | PVString !String
  deriving stock (Eq, Ord, Show)

data Sym = SymNamed !String | SymAnon
  deriving stock (Eq, Ord, Show)

instance IsString Sym where
  fromString = SymNamed

data Sort = SortUnint !String | SortBool
  deriving stock (Eq, Ord, Show)

data Decl = Decl ![Sort] !Sort
  deriving stock (Eq, Ord, Show)

data LocalSt = LocalSt
  { lsNextSym :: !Int
  , lsDecls :: !(Map String Decl)
  }
  deriving stock (Eq, Ord, Show)

initLocalSt :: LocalSt
initLocalSt = LocalSt 0 Map.empty

-- Hacking around Z3Env private constructor :(
data RemoteSt = RemoteSt
  { rsSolver :: !ZB.Solver
  , rsContext :: !ZB.Context
  , rsFixedpoint :: !ZB.Fixedpoint
  , rsOptimize :: !ZB.Optimize
  }

newRemoteSt :: IO RemoteSt
newRemoteSt =
  let mbLogic = Nothing
      opts = mempty
  in  ZB.withConfig $ \cfg -> do
        ZO.setOpts cfg opts
        ctx <- ZB.mkContext cfg
        solver <- maybe (ZB.mkSolver ctx) (ZB.mkSolverForLogic ctx) mbLogic
        fixedpoint <- ZB.mkFixedpoint ctx
        optimize <- ZB.mkOptimize ctx
        return (RemoteSt solver ctx fixedpoint optimize)

data SolveSt = St
  { ssLocal :: !(IORef LocalSt)
  , ssRemote :: !RemoteSt
  }

newSolveSt :: (MonadIO m) => m SolveSt
newSolveSt = liftIO $ do
  local <- newIORef initLocalSt
  remote <- newRemoteSt
  pure (St local remote)

data Err
  = ErrDupeDecl !String
  | ErrMissingDecl !String
  deriving stock (Eq, Ord, Show)

instance Exception Err

newtype SolveM a = SolveM {unSolveM :: ReaderT SolveSt (ExceptT Err IO) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError Err)

instance Z.MonadZ3 SolveM where
  getSolver = SolveM (asks (rsSolver . ssRemote))
  getContext = SolveM (asks (rsContext . ssRemote))

instance Z.MonadFixedpoint SolveM where
  getFixedpoint = SolveM (asks (rsFixedpoint . ssRemote))

instance MonadState LocalSt SolveM where
  get = SolveM (ask >>= liftIO . readIORef . ssLocal)
  put st = SolveM (ask >>= liftIO . flip writeIORef st . ssLocal)
  state f = SolveM (ask >>= liftIO . flip atomicModifyIORef' (swap . f) . ssLocal)

runSolveM :: SolveM a -> SolveSt -> IO (Either Err a)
runSolveM m = runExceptT . runReaderT (unSolveM m)

withSolveM :: (MonadIO m) => SolveM a -> m a
withSolveM m = newSolveSt >>= flip solve m

solve :: (MonadIO m) => SolveSt -> SolveM a -> m a
solve ss m = liftIO (runSolveM m ss >>= either throwIO pure)

getM :: (LocalSt -> SolveM a) -> SolveM a
getM f = do
  r <- SolveM (asks ssLocal)
  st0 <- liftIO (readIORef r)
  f st0

stateM :: (LocalSt -> SolveM (a, LocalSt)) -> SolveM a
stateM f = do
  r <- SolveM (asks ssLocal)
  st0 <- liftIO (readIORef r)
  (a, st1) <- f st0
  liftIO (writeIORef r st1)
  pure a

modifyM :: (LocalSt -> SolveM LocalSt) -> SolveM ()
modifyM f = do
  r <- SolveM (asks ssLocal)
  st0 <- liftIO (readIORef r)
  st1 <- f st0
  liftIO (writeIORef r st1)

mkParams :: Params -> SolveM Z.Params
mkParams pm = do
  pz <- Z.mkParams
  for_ (Map.toList pm) $ \(k, v) -> do
    k' <- Z.mkStringSymbol k
    case v of
      PVBool x -> Z.paramsSetBool pz k' x
      PVWord x -> Z.paramsSetUInt pz k' x
      PVDouble x -> Z.paramsSetDouble pz k' x
      PVString x -> Z.mkStringSymbol x >>= Z.paramsSetSymbol pz k'
  pure pz

mkSym :: Sym -> SolveM Z.Symbol
mkSym = \case
  SymNamed n -> Z.mkStringSymbol n
  SymAnon -> stateM $ \ls -> do
    let i = ls.lsNextSym
        st' = ls {lsNextSym = i + 1}
    x <- Z.mkIntSymbol i
    pure (x, st')

mkSort :: Sort -> SolveM Z.Sort
mkSort = \case
  SortUnint n -> Z.mkStringSymbol n >>= Z.mkUninterpretedSort
  SortBool -> Z.mkBoolSort

mkDeclSort :: Decl -> SolveM Z.Sort
mkDeclSort (Decl args ret) = case args of
  [] -> mkSort ret
  _ -> error "TODO"

mkExpF :: ExpF Z.AST -> SolveM Z.AST
mkExpF = \case
  ExpVarF x -> do
    md <- gets (Map.lookup x . lsDecls)
    sort' <- case md of
      Nothing -> throwError (ErrMissingDecl x)
      Just d -> mkDeclSort d
    sym' <- mkSym (SymNamed x)
    Z.mkVar sym' sort'
  ExpBoolF x -> Z.mkBool x
  ExpEqF x y -> Z.mkEq x y
  ExpNotF x -> Z.mkNot x
  ExpIteF x y z -> Z.mkIte x y z
  ExpIffF x y -> Z.mkIff x y
  ExpImpliesF x y -> Z.mkImplies x y
  ExpXorF x y -> Z.mkXor x y
  ExpAndF xs -> Z.mkAnd xs
  ExpOrF xs -> Z.mkOr xs
  ExpDistinctF xs -> Z.mkDistinct xs

mkExp :: Exp -> SolveM Z.AST
mkExp = cata (sequence >=> mkExpF)

mkFuncDecl :: String -> Decl -> SolveM Z.FuncDecl
mkFuncDecl name (Decl args ty) = do
  name' <- mkSym (SymNamed name)
  args' <- traverse mkSort args
  ty' <- mkSort ty
  Z.mkFuncDecl name' args' ty'

getDecl :: String -> SolveM Decl
getDecl name = getM $ \ls ->
  case Map.lookup name ls.lsDecls of
    Nothing -> throwError (ErrMissingDecl name)
    Just d -> pure d

setDecl :: String -> Decl -> SolveM ()
setDecl name decl = modifyM $ \ls ->
  case Map.lookup name ls.lsDecls of
    Nothing ->
      let decls = Map.insert name decl ls.lsDecls
      in  pure ls {lsDecls = decls}
    Just _ -> throwError (ErrDupeDecl name)

relation :: String -> [Sort] -> Sort -> SolveM ()
relation name args ty = do
  let decl = Decl args ty
  decl' <- mkFuncDecl name decl
  Z.fixedpointRegisterRelation decl'
  setDecl name decl

rule :: Exp -> SolveM ()
rule e = do
  e' <- mkExp e
  s' <- mkSym SymAnon
  Z.fixedpointAddRule e' s'

query :: [String] -> SolveM Z.Result
query names = do
  decls' <- traverse (\name -> getDecl name >>= mkFuncDecl name) names
  Z.fixedpointQueryRelations decls'

params :: Params -> SolveM ()
params = mkParams >=> Z.fixedpointSetParams

-- TODO convert the returned AST

answer :: SolveM Z.AST
answer = Z.fixedpointGetAnswer

assertions :: SolveM [Z.AST]
assertions = Z.fixedpointGetAssertions
