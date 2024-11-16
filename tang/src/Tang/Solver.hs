module Tang.Solver where

import Control.Exception (Exception, throwIO)
import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), ask, asks)
import Control.Monad.State.Strict (MonadState (..))
import Data.Foldable (for_)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.String (IsString (..))
import Data.Tuple (swap)
import Tang.Exp (Def (..), Tm (..), TmDef (..), TmF (..), Ty (..), TyDef (..))
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

data LocalSt = LocalSt
  { lsNextSym :: !Int
  , lsDefs :: !(Map String Def)
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
  fmap (St local) newRemoteSt

data Err
  = ErrDupeDef !String
  | ErrMissingDef !String
  | ErrNotTm !String
  | ErrNotTy !String
  | ErrReflect !String
  | ErrArityMismatch !String !Int !Int
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

getDef :: String -> SolveM Def
getDef name = getM $ \ls ->
  case Map.lookup name ls.lsDefs of
    Nothing -> throwError (ErrMissingDef name)
    Just d -> pure d

getTmDef :: String -> SolveM TmDef
getTmDef name = do
  d <- getDef name
  case d of
    DefTy _ -> throwError (ErrNotTm name)
    DefTm tmd -> pure tmd

getTyDef :: String -> SolveM TyDef
getTyDef name = do
  d <- getDef name
  case d of
    DefTm _ -> throwError (ErrNotTy name)
    DefTy tyd -> pure tyd

setDef :: String -> Def -> SolveM ()
setDef name d = modifyM $ \ls ->
  case Map.lookup name ls.lsDefs of
    Nothing ->
      let defs = Map.insert name d ls.lsDefs
      in  pure ls {lsDefs = defs}
    Just _ -> throwError (ErrDupeDef name)

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

mkSort :: Ty -> SolveM Z.Sort
mkSort = \case
  TyVar n -> do
    TyDef mty <- getTyDef n
    case mty of
      Nothing -> Z.mkStringSymbol n >>= Z.mkUninterpretedSort
      Just ty -> mkSort ty
  TyBool -> Z.mkBoolSort
  TyBv i -> Z.mkBvSort i

mkFuncDecl :: String -> TmDef -> SolveM Z.FuncDecl
mkFuncDecl name (TmDef args ret) = do
  name' <- Z.mkStringSymbol name
  args' <- traverse mkSort args
  ret' <- mkSort ret
  Z.mkFuncDecl name' args' ret'

mkTmF :: TmF Z.AST -> SolveM Z.AST
mkTmF = \case
  TmVarF x -> do
    tmd@(TmDef args _) <- getTmDef x
    case args of
      [] -> do
        fd' <- mkFuncDecl x tmd
        Z.mkApp fd' []
      _ -> throwError (ErrArityMismatch x (length args) 0)
  TmBoolF x -> Z.mkBool x
  TmEqF x y -> Z.mkEq x y
  TmNotF x -> Z.mkNot x
  TmIteF x y z -> Z.mkIte x y z
  TmIffF x y -> Z.mkIff x y
  TmImpliesF x y -> Z.mkImplies x y
  TmXorF x y -> Z.mkXor x y
  TmAndF xs -> Z.mkAnd xs
  TmOrF xs -> Z.mkOr xs
  TmDistinctF xs -> Z.mkDistinct xs
  TmAppF x y -> do
    tmd@(TmDef args _) <- getTmDef x
    let actualAr = length args
        expectedAr = length y
    if actualAr == expectedAr
      then do
        fd' <- mkFuncDecl x tmd
        Z.mkApp fd' y
      else throwError (ErrArityMismatch x actualAr expectedAr)

mkTm :: Tm -> SolveM Z.AST
mkTm = cata (sequence >=> mkTmF)

reflect :: Z.AST -> SolveM Tm
reflect t = do
  k <- Z.getAstKind t
  case k of
    Z.Z3_APP_AST -> do
      app' <- Z.toApp t
      def' <- Z.getAppDecl app'
      name' <- Z.getDeclName def'
      name <- Z.getSymbolString name'
      args' <- Z.getAppArgs app'
      args <- traverse reflect args'
      pure $ case name of
        "and" -> TmAnd args
        "or" -> TmOr args
        "true" -> TmBool True
        "false" -> TmBool False
        _ -> case args of
          [] -> TmVar name
          _ -> TmApp name args
    _ -> throwError (ErrReflect (show k))

defConst :: String -> Ty -> SolveM ()
defConst name ty = setDef name (DefTm (TmDef [] ty))

defFun :: String -> [Ty] -> Ty -> SolveM ()
defFun name args ret = setDef name (DefTm (TmDef args ret))

defTy :: String -> Maybe Ty -> SolveM ()
defTy name mty = setDef name (DefTy (TyDef mty))

defRel :: String -> [Ty] -> Ty -> SolveM ()
defRel name args ret = do
  let tmd = TmDef args ret
  def <- mkFuncDecl name tmd
  Z.fixedpointRegisterRelation def
  setDef name (DefTm tmd)

defRule :: Tm -> SolveM ()
defRule e = do
  e' <- mkTm e
  s' <- mkSym SymAnon
  Z.fixedpointAddRule e' s'

query :: [String] -> SolveM Z.Result
query names = do
  decls' <- traverse (\n -> getTmDef n >>= mkFuncDecl n) names
  Z.fixedpointQueryRelations decls'

params :: Params -> SolveM ()
params = mkParams >=> Z.fixedpointSetParams

-- NOTE might only be valid after query, otherwise error
answer :: SolveM Tm
answer = Z.fixedpointGetAnswer >>= reflect

-- NOTE might only be valid after query, otherwise err
assertions :: SolveM [Tm]
assertions = Z.fixedpointGetAssertions >>= traverse reflect
