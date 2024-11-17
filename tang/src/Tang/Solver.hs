module Tang.Solver where

import Control.Exception (Exception, throwIO)
import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), ask, asks)
import Control.Monad.State.Strict (MonadState (..), execStateT, gets, modify')
import Control.Monad.Trans (lift)
import Data.Foldable (for_, toList)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Tuple (swap)
import Tang.Exp (Tm (..), TmF (..), Ty (..))
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

data Role = RoleUninterp | RoleVar | RoleRel
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data TmDef = TmDef !Role ![Ty] !Ty
  deriving stock (Eq, Ord, Show)

-- Nothing means uninterpreted
newtype TyDef = TyDef (Maybe Ty)
  deriving stock (Eq, Ord, Show)

data ZTmDef = ZTmDef !TmDef !Z.FuncDecl
  deriving stock (Eq, Ord, Show)

data ZTyDef = ZTyDef !TyDef !Z.Sort
  deriving stock (Eq, Ord, Show)

data ZDef
  = ZDefTm !ZTmDef
  | ZDefTy !ZTyDef
  deriving stock (Eq, Ord, Show)

data LocalSt = LocalSt
  { lsNextSym :: !Int
  , lsDefs :: !(Map String ZDef)
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
  | ErrNotVar !String
  | ErrReflect !String
  | ErrArityMismatch !String !Int !Int
  | ErrNotIntTy !Ty
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

lookupDef :: String -> SolveM (Maybe ZDef)
lookupDef name = gets (Map.lookup name . lsDefs)

getDef :: String -> SolveM ZDef
getDef name = do
  md <- lookupDef name
  case md of
    Nothing -> throwError (ErrMissingDef name)
    Just d -> pure d

projectTm :: String -> ZDef -> SolveM ZTmDef
projectTm name = \case
  ZDefTm z -> pure z
  _ -> throwError (ErrNotTm name)

projectTy :: String -> ZDef -> SolveM ZTyDef
projectTy name = \case
  ZDefTy z -> pure z
  _ -> throwError (ErrNotTm name)

lookupTm :: String -> SolveM (Maybe ZTmDef)
lookupTm name = lookupDef name >>= traverse (projectTm name)

getTm :: String -> SolveM ZTmDef
getTm name = getDef name >>= projectTm name

lookupTy :: String -> SolveM (Maybe ZTyDef)
lookupTy name = lookupDef name >>= traverse (projectTy name)

getTy :: String -> SolveM ZTyDef
getTy name = getDef name >>= projectTy name

setDef :: String -> ZDef -> SolveM ()
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

getSort :: Ty -> SolveM Z.Sort
getSort = \case
  TyVar n -> fmap (\(ZTyDef _ z) -> z) (getTy n)
  TyBool -> Z.mkBoolSort
  TyBv i -> Z.mkBvSort i

getOrCreateSort :: String -> Maybe Ty -> SolveM Z.Sort
getOrCreateSort name = \case
  Nothing -> Z.mkStringSymbol name >>= Z.mkUninterpretedSort
  Just ty -> getSort ty

mkIntSort :: Ty -> SolveM Z.Sort
mkIntSort ty = do
  case ty of
    TyBv _ -> pure ()
    _ -> throwError (ErrNotIntTy ty)
  getSort ty

mkFuncDecl :: String -> TmDef -> SolveM Z.FuncDecl
mkFuncDecl name (TmDef _ args ret) = do
  name' <- Z.mkStringSymbol name
  args' <- traverse getSort args
  ret' <- getSort ret
  Z.mkFuncDecl name' args' ret'

mkTmF :: TmF Z.AST -> SolveM Z.AST
mkTmF = \case
  TmVarF x -> do
    ZTmDef (TmDef _ args _) fd' <- getTm x
    case args of
      [] -> Z.mkApp fd' []
      _ -> throwError (ErrArityMismatch x (length args) 0)
  TmBoolF x -> Z.mkBool x
  TmIntF ty x -> do
    sort' <- mkIntSort ty
    Z.mkInt x sort'
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
    ZTmDef (TmDef _ args _) fd' <- getTm x
    let actualAr = length args
        expectedAr = length y
    if actualAr == expectedAr
      then Z.mkApp fd' y
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

defVar :: String -> Ty -> SolveM ()
defVar name = defFun' RoleVar name []

defConst :: String -> Ty -> SolveM ()
defConst name = defFun name []

defFun :: String -> [Ty] -> Ty -> SolveM ()
defFun = defFun' RoleUninterp

defFun' :: Role -> String -> [Ty] -> Ty -> SolveM ()
defFun' role name args ret = do
  let tmd = TmDef role args ret
  fd' <- mkFuncDecl name tmd
  setDef name (ZDefTm (ZTmDef tmd fd'))

defTy :: String -> Maybe Ty -> SolveM ()
defTy name mty = do
  sort' <- getOrCreateSort name mty
  setDef name (ZDefTy (ZTyDef (TyDef mty) sort'))

defRel :: String -> [Ty] -> SolveM ()
defRel name args = do
  let tmd = TmDef RoleRel args TyBool
  fd' <- mkFuncDecl name tmd
  Z.fixedpointRegisterRelation fd'
  setDef name (ZDefTm (ZTmDef tmd fd'))

gatherVars :: Tm -> SolveM (Set String)
gatherVars tm0 = execStateT (cata go tm0) Set.empty
 where
  go tm = case tm of
    TmVarF x -> do
      (ZTmDef (TmDef role _ _) _) <- lift (getTm x)
      case role of
        RoleVar -> modify' (Set.insert x)
        _ -> pure ()
    _ -> sequence_ tm

defRule :: Tm -> SolveM ()
defRule e = do
  vars <- gatherVars e
  e' <- mkTm e
  q' <-
    if Set.null vars
      then pure e'
      else do
        apps' <- traverse (mkTm . TmVar >=> Z.toApp) (toList vars)
        Z.mkForallConst [] apps' e'
  s' <- mkSym SymAnon
  Z.fixedpointAddRule q' s'

query :: [String] -> SolveM Z.Result
query names = do
  decls' <- traverse (fmap (\(ZTmDef _ z) -> z) . getTm) names
  Z.fixedpointQueryRelations decls'

params :: Params -> SolveM ()
params = mkParams >=> Z.fixedpointSetParams

-- NOTE might only be valid after query, otherwise error
answer :: SolveM Tm
answer = Z.fixedpointGetAnswer >>= reflect

-- NOTE might only be valid after query, otherwise err
assertions :: SolveM [Tm]
assertions = Z.fixedpointGetAssertions >>= traverse reflect
