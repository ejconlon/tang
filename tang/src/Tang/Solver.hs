module Tang.Solver
  ( Params
  , PVal (..)
  , Err (..)
  , SolveSt
  , newSolveSt
  , SolveT
  , SolveM
  , runSolveT
  , runSolveM
  , withSolveM
  , solve
  , defVar
  , defConst
  , defFun
  , defRel
  , defTy
  , defRule
  , query
  , answer
  , params
  , assert
  , assertWith
  , check
  , model
  , SolveListM
  , liftS
  , nextS
  , unfoldS
  )
where

import Control.Applicative (Alternative (..))
import Control.Exception (Exception, throwIO)
import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), ask, asks)
import Control.Monad.State.Strict (MonadState (..), execStateT, gets, modify')
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.Foldable (foldl', for_)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Traversable (for)
import Data.Tuple (swap)
import ListT (ListT, uncons)
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

newtype SolveT m a = SolveT {unSolveT :: ReaderT SolveSt (ExceptT Err m) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError Err)

type SolveM = SolveT IO

instance (MonadIO m) => Z.MonadZ3 (SolveT m) where
  getSolver = SolveT (asks (rsSolver . ssRemote))
  getContext = SolveT (asks (rsContext . ssRemote))

instance (MonadIO m) => Z.MonadFixedpoint (SolveT m) where
  getFixedpoint = SolveT (asks (rsFixedpoint . ssRemote))

instance (MonadIO m) => MonadState LocalSt (SolveT m) where
  get = SolveT (ask >>= liftIO . readIORef . ssLocal)
  put st = SolveT (ask >>= liftIO . flip writeIORef st . ssLocal)
  state f = SolveT (ask >>= liftIO . flip atomicModifyIORef' (swap . f) . ssLocal)

runSolveT :: SolveT m a -> SolveSt -> m (Either Err a)
runSolveT m = runExceptT . runReaderT (unSolveT m)

runSolveM :: SolveM a -> SolveSt -> IO (Either Err a)
runSolveM = runSolveT

withSolveM :: (MonadIO m) => SolveM a -> m a
withSolveM m = newSolveSt >>= flip solve m

solve :: (MonadIO m) => SolveSt -> SolveM a -> m a
solve ss m = liftIO (runSolveM m ss >>= either throwIO pure)

getM :: (MonadIO m) => (LocalSt -> SolveT m a) -> SolveT m a
getM f = do
  r <- SolveT (asks ssLocal)
  st0 <- liftIO (readIORef r)
  f st0

stateM :: (MonadIO m) => (LocalSt -> SolveT m (a, LocalSt)) -> SolveT m a
stateM f = do
  r <- SolveT (asks ssLocal)
  st0 <- liftIO (readIORef r)
  (a, st1) <- f st0
  liftIO (writeIORef r st1)
  pure a

modifyM :: (MonadIO m) => (LocalSt -> SolveT m LocalSt) -> SolveT m ()
modifyM f = do
  r <- SolveT (asks ssLocal)
  st0 <- liftIO (readIORef r)
  st1 <- f st0
  liftIO (writeIORef r st1)

lookupDef :: (MonadIO m) => String -> SolveT m (Maybe ZDef)
lookupDef name = gets (Map.lookup name . lsDefs)

getDef :: (MonadIO m) => String -> SolveT m ZDef
getDef name = do
  md <- lookupDef name
  case md of
    Nothing -> throwError (ErrMissingDef name)
    Just d -> pure d

projectTm :: (Monad m) => String -> ZDef -> SolveT m ZTmDef
projectTm name = \case
  ZDefTm z -> pure z
  _ -> throwError (ErrNotTm name)

projectTy :: (Monad m) => String -> ZDef -> SolveT m ZTyDef
projectTy name = \case
  ZDefTy z -> pure z
  _ -> throwError (ErrNotTm name)

lookupTm :: (MonadIO m) => String -> SolveT m (Maybe ZTmDef)
lookupTm name = lookupDef name >>= traverse (projectTm name)

getTm :: (MonadIO m) => String -> SolveT m ZTmDef
getTm name = getDef name >>= projectTm name

lookupTy :: (MonadIO m) => String -> SolveT m (Maybe ZTyDef)
lookupTy name = lookupDef name >>= traverse (projectTy name)

getTy :: (MonadIO m) => String -> SolveT m ZTyDef
getTy name = getDef name >>= projectTy name

setDef :: (MonadIO m) => String -> ZDef -> SolveT m ()
setDef name d = modifyM $ \ls ->
  case Map.lookup name ls.lsDefs of
    Nothing ->
      let defs = Map.insert name d ls.lsDefs
      in  pure ls {lsDefs = defs}
    Just _ -> throwError (ErrDupeDef name)

mkParams :: (MonadIO m) => Params -> SolveT m Z.Params
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

mkSym :: (MonadIO m) => Sym -> SolveT m Z.Symbol
mkSym = \case
  SymNamed n -> Z.mkStringSymbol n
  SymAnon -> stateM $ \ls -> do
    let i = ls.lsNextSym
        st' = ls {lsNextSym = i + 1}
    x <- Z.mkIntSymbol i
    pure (x, st')

getSort :: (MonadIO m) => Ty -> SolveT m Z.Sort
getSort = \case
  TyVar n -> fmap (\(ZTyDef _ z) -> z) (getTy n)
  TyBool -> Z.mkBoolSort
  TyBv i -> Z.mkBvSort i

getOrCreateSort :: (MonadIO m) => String -> Maybe Ty -> SolveT m Z.Sort
getOrCreateSort name = \case
  Nothing -> Z.mkStringSymbol name >>= Z.mkUninterpretedSort
  Just ty -> getSort ty

mkIntSort :: (MonadIO m) => Ty -> SolveT m Z.Sort
mkIntSort ty = do
  case ty of
    TyBv _ -> pure ()
    _ -> throwError (ErrNotIntTy ty)
  getSort ty

mkFuncDecl :: (MonadIO m) => String -> TmDef -> SolveT m Z.FuncDecl
mkFuncDecl name (TmDef _ args ret) = do
  name' <- Z.mkStringSymbol name
  args' <- traverse getSort args
  ret' <- getSort ret
  Z.mkFuncDecl name' args' ret'

mkTmF :: (MonadIO m) => EnvTo -> TmF Z.AST -> SolveT m Z.AST
mkTmF env = \case
  TmVarF x -> do
    case Map.lookup x env of
      Just (Arg i ty) -> do
        sort' <- getSort ty
        Z.mkBound i sort'
      Nothing -> do
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

mkTm :: (MonadIO m) => EnvTo -> Tm -> SolveT m Z.AST
mkTm env = cata (sequence >=> mkTmF env)

assertArity :: (Monad m) => String -> [a] -> Int -> b -> SolveT m b
assertArity name as expected b =
  let actual = length as
  in  if actual == expected
        then pure b
        else throwError (ErrArityMismatch name actual expected)

data Arg k = Arg {argKey :: !k, argTy :: !Ty}
  deriving stock (Eq, Ord, Show)

type EnvTo = Map String (Arg Int)

type EnvFrom = IntMap (Arg String)

-- data Env = Env !EnvTo !EnvFrom
--   deriving stock (Eq, Ord, Show)

funcEnv :: (MonadIO m) => String -> [String] -> SolveT m EnvFrom
funcEnv funcName argNames = do
  ZTmDef (TmDef _ argTys _) _ <- getTm funcName
  let actual = length argTys
      expected = length argNames
  if actual == expected
    then pure (IntMap.fromAscList (zip [0 ..] (fmap (uncurry Arg) (zip argNames argTys))))
    else throwError (ErrArityMismatch funcName actual expected)

reflectTy :: (MonadIO m) => Z.Sort -> SolveT m Ty
reflectTy s = do
  k <- Z.getSortKind s
  case k of
    Z.Z3_BV_SORT -> fmap TyBv (Z.getBvSortSize s)
    -- Z3_UNINTERPRETED_SORT
    -- Z3_BOOL_SORT
    -- Z3_INT_SORT
    -- Z3_REAL_SORT
    -- Z3_BV_SORT
    -- Z3_ARRAY_SORT
    -- Z3_DATATYPE_SORT
    -- Z3_RELATION_SORT
    -- Z3_FINITE_DOMAIN_SORT
    -- Z3_FLOATING_POINT_SORT
    -- Z3_ROUNDING_MODE_SORT
    -- Z3_UNKNOWN_SORT
    _ -> error "TODO expand reflectTy"

reflectIntTy :: (MonadIO m) => Ty -> Z.AST -> SolveT m Tm
reflectIntTy ty t = case ty of
  TyBv _ -> fmap (TmInt ty . fromInteger) (Z.getInt t)
  _ -> throwError (ErrNotIntTy ty)

reflectTm :: (MonadIO m) => EnvFrom -> Z.AST -> SolveT m Tm
reflectTm env = go
 where
  go t = do
    k <- Z.getAstKind t
    case k of
      Z.Z3_APP_AST -> do
        app' <- Z.toApp t
        def' <- Z.getAppDecl app'
        name' <- Z.getDeclName def'
        name <- Z.getSymbolString name'
        args' <- Z.getAppArgs app'
        args <- traverse go args'
        let f = assertArity name args
        case name of
          "and" -> pure (TmAnd args)
          "or" -> pure (TmOr args)
          "true" -> f 0 (TmBool True)
          "false" -> f 0 (TmBool False)
          "=" -> f 2 $ case args of
            [a1, a2] -> TmEq a1 a2
            _ -> error "impossible"
          _ -> case args of
            [] -> pure (TmVar name)
            _ -> pure (TmApp name args)
      Z.Z3_VAR_AST -> do
        i <- Z.getIndexValue t
        case IntMap.lookup i env of
          Nothing -> throwError (ErrReflect ("Invalid index: " ++ show t))
          Just (Arg n _) -> pure (TmVar n)
      Z.Z3_NUMERAL_AST -> do
        ty <- Z.getSort t >>= reflectTy
        reflectIntTy ty t
      _ -> throwError (ErrReflect ("Unsupported type: " ++ show k))

defVar :: (MonadIO m) => String -> Ty -> SolveT m ()
defVar name = defFun' RoleVar name []

defConst :: (MonadIO m) => String -> Ty -> SolveT m ()
defConst name = defFun name []

defFun :: (MonadIO m) => String -> [Ty] -> Ty -> SolveT m ()
defFun = defFun' RoleUninterp

defFun' :: (MonadIO m) => Role -> String -> [Ty] -> Ty -> SolveT m ()
defFun' role name args ret = do
  let tmd = TmDef role args ret
  fd' <- mkFuncDecl name tmd
  setDef name (ZDefTm (ZTmDef tmd fd'))

defTy :: (MonadIO m) => String -> Maybe Ty -> SolveT m ()
defTy name mty = do
  sort' <- getOrCreateSort name mty
  setDef name (ZDefTy (ZTyDef (TyDef mty) sort'))

defRel :: (MonadIO m) => String -> [Ty] -> SolveT m ()
defRel name args = do
  let tmd = TmDef RoleRel args TyBool
  fd' <- mkFuncDecl name tmd
  Z.fixedpointRegisterRelation fd'
  setDef name (ZDefTm (ZTmDef tmd fd'))

gatherVars :: (MonadIO m) => Tm -> SolveT m (Map String Ty)
gatherVars tm0 = execStateT (cata go tm0) Map.empty
 where
  go tm = case tm of
    TmVarF x -> do
      (ZTmDef (TmDef role _ ty) _) <- lift (getTm x)
      case role of
        RoleVar -> modify' (Map.insert x ty)
        _ -> pure ()
    _ -> sequence_ tm

mkEnvTo :: Map String Ty -> EnvTo
mkEnvTo = foldl' go Map.empty . zip [0 ..] . Map.toList
 where
  go m (i, (k, ty)) = Map.insert k (Arg i ty) m

mkExplicitForall :: (MonadIO m) => EnvTo -> Tm -> SolveT m Z.AST
mkExplicitForall env e = do
  e' <- mkTm env e
  if Map.null env
    then pure e'
    else do
      syms' <- traverse Z.mkStringSymbol (Map.keys env)
      sorts' <- traverse (getSort . argTy) (Map.elems env)
      Z.mkForall [] syms' sorts' e'

mkImplicitForall :: (MonadIO m) => Tm -> SolveT m Z.AST
mkImplicitForall e = do
  vars <- gatherVars e
  let env = mkEnvTo vars
  mkExplicitForall env e

defRule :: (MonadIO m) => Tm -> [Tm] -> SolveT m ()
defRule hd tl = do
  let e = case tl of
        [] -> hd
        [x] -> TmImplies x hd
        _ -> TmImplies (TmAnd tl) hd
  q' <- mkImplicitForall e
  s' <- mkSym SymAnon
  Z.fixedpointAddRule q' s'

query :: (MonadIO m) => String -> SolveT m Z.Result
query funcName = do
  decl' <- fmap (\(ZTmDef _ z) -> z) (getTm funcName)
  Z.fixedpointQueryRelations [decl']

answer :: (MonadIO m) => String -> [String] -> SolveT m (Maybe Tm)
answer funcName argNames = do
  env <- funcEnv funcName argNames
  res <- query funcName
  case res of
    Z.Sat -> fmap Just (Z.fixedpointGetAnswer >>= reflectTm env)
    _ -> pure Nothing

params :: (MonadIO m) => Params -> SolveT m ()
params = mkParams >=> Z.fixedpointSetParams

assert :: (MonadIO m) => Tm -> SolveT m ()
assert = mkImplicitForall >=> Z.assert

assertWith :: (MonadIO m) => [(String, Ty)] -> Tm -> SolveT m ()
assertWith vars = mkExplicitForall (mkEnvTo (Map.fromList vars)) >=> Z.assert

check :: (MonadIO m) => SolveT m Z.Result
check = Z.check

data FuncEntry = FuncEntry
  { feArgs :: ![Tm]
  , feValue :: !Tm
  }
  deriving stock (Eq, Ord, Show)

reflectFuncEntry :: (MonadIO m) => Z.FuncEntry -> SolveT m FuncEntry
reflectFuncEntry fe = do
  let f = reflectTm IntMap.empty
  numArgs <- Z.funcEntryGetNumArgs fe
  args <- traverse (Z.funcEntryGetArg fe >=> f) [0 .. numArgs - 1]
  value <- Z.funcEntryGetValue fe >>= f
  pure (FuncEntry args value)

data FuncInterp = FuncInterp
  { feEntries :: ![FuncEntry]
  , feElseCase :: !(Maybe Tm)
  }
  deriving stock (Eq, Ord, Show)

reflectFuncInterp :: (MonadIO m) => Z.FuncInterp -> SolveT m FuncInterp
reflectFuncInterp fi = do
  numEntries <- Z.funcInterpGetNumEntries fi
  entries <- traverse (Z.funcInterpGetEntry fi >=> reflectFuncEntry) [0 .. numEntries - 1]
  ec' <- Z.funcInterpGetElse fi
  ecKind' <- Z.getAstKind ec'
  ec <- case ecKind' of
    Z.Z3_UNKNOWN_AST -> pure Nothing
    _ -> fmap Just (reflectTm IntMap.empty ec')
  pure (FuncInterp entries ec)

data Interp = InterpConst !Tm | InterpFunc !FuncInterp
  deriving stock (Eq, Ord, Show)

type Model = Map String Interp

reflectMod :: (MonadIO m) => Z.Model -> SolveT m Model
reflectMod m = do
  consts <- Z.getConsts m
  constInterps <- for consts $ \x -> do
    name <- Z.getDeclName x >>= Z.getSymbolString
    my <- Z.getConstInterp m x
    z <- case my of
      Nothing -> error "impossible"
      Just y -> reflectTm IntMap.empty y
    pure (name, InterpConst z)
  funcs <- Z.getConsts m
  funcInterps <- for funcs $ \x -> do
    name <- Z.getDeclName x >>= Z.getSymbolString
    my <- Z.getFuncInterp m x
    z <- case my of
      Nothing -> error "impossible"
      Just y -> reflectFuncInterp y
    pure (name, InterpFunc z)
  pure (Map.fromList constInterps <> Map.fromList funcInterps)

model :: (MonadIO m) => SolveT m (Maybe Model)
model = fmap snd (Z.withModel reflectMod)

-- private
push :: (MonadIO m) => SolveT m LocalSt
push = do
  ls <- get
  Z.push
  pure ls

-- private
pop :: (MonadIO m) => LocalSt -> SolveT m ()
pop ls = do
  Z.pop 1
  put ls

newtype SolveListM a = SolveListM {unSolveListM :: ListT SolveM a}
  deriving newtype (Functor, Applicative, Monad)

instance Alternative SolveListM where
  empty = SolveListM empty
  s1 <|> s2 = SolveListM (unSolveListM (restoring s1) <|> unSolveListM (restoring s2))

-- private
ensuring :: SolveM () -> ListT SolveM a -> ListT SolveM a
ensuring cleanup act = catchError act (\e -> lift cleanup >> throwError e) >>= \a -> a <$ lift cleanup

-- private
restoring :: SolveListM a -> SolveListM a
restoring (SolveListM act) = SolveListM $ do
  ls <- lift push
  ensuring (pop ls) act

liftS :: SolveM a -> SolveListM a
liftS = SolveListM . lift

nextS :: SolveListM a -> SolveM (Maybe (a, SolveListM a))
nextS = fmap (fmap (second SolveListM)) . uncons . unSolveListM

unfoldS :: b -> SolveListM a -> (b -> a -> Either b b) -> SolveM b
unfoldS b0 m0 f = push >>= \ls -> go b0 m0 >>= \bx -> bx <$ pop ls
 where
  go !b1 m1 = do
    mx <- nextS m1
    case mx of
      Nothing -> pure b1
      Just (a, m2) ->
        case f b1 a of
          Left b2 -> go b2 m2
          Right b2 -> pure b2
