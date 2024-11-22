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
  , defVars
  , defConst
  , defConsts
  , defFun
  , defFuns
  , defTy
  , defTys
  , assert
  , assertWith
  , check
  , FuncEntry (..)
  , FuncInterp (..)
  , Interp (..)
  , Model
  , model
  , SolveListM
  , liftS
  , nextS
  , unfoldS
  )
where

import Control.Applicative (Alternative (..))
import Control.Exception (Exception, throwIO)
import Control.Monad (unless, (>=>))
import Control.Monad.Except (Except, ExceptT, MonadError (..), runExcept, runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Control.Monad.State.Strict (MonadState (..), execStateT, gets, modify')
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.Foldable (foldl', for_, traverse_)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.String (IsString (..))
import Data.Tuple (swap)
import ListT (ListT, uncons)
import Tang.Exp (Tm (..), TmF (..), Ty (..), Val (..), expVal)
import Tang.Util (andAllM, foldM', orAllM)
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

instance Data.String.IsString Sym where
  fromString = SymNamed

data Role = RoleUninterp | RoleVar | RoleRel
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data TmDef = TmDef !Role ![(String, Ty)] !Ty
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
  loc <- newIORef initLocalSt
  fmap (St loc) newRemoteSt

data Err
  = ErrDupeDef !String
  | ErrMissingDef !String
  | ErrNotTm !String
  | ErrNotTy !String
  | ErrNotVar !String
  | ErrReflect !String
  | ErrArityMismatch !String !Int !Int
  | ErrNotIntTy !Ty
  | ErrVar !VarErr
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
  args' <- traverse (getSort . snd) args
  ret' <- getSort ret
  Z.mkFuncDecl name' args' ret'

mkTmF :: (MonadIO m) => EnvTo -> TmF Z.AST -> SolveT m Z.AST
mkTmF env = \case
  TmVarF x -> do
    case Map.lookup x env of
      Just (Arg i ty) -> do
        sort' <- getSort ty
        -- NOTE: Bound vars are Debruijn indices
        Z.mkBound (Map.size env - i - 1) sort'
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
  TmLtF x y -> Z.mkBvult x y -- TODO check type Z.mkLt x y
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

mkEnvFrom :: (MonadIO m) => String -> SolveT m ([String], EnvFrom)
mkEnvFrom funcName = do
  ZTmDef (TmDef _ argPairs _) _ <- getTm funcName
  let names = fmap fst argPairs
      env = IntMap.fromAscList (zip [0 ..] (fmap (uncurry Arg) argPairs))
  pure (names, env)

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
          "<" -> f 2 $ case args of
            [a1, a2] -> TmLt a1 a2
            _ -> error "impossible"
          _ -> case args of
            [] -> pure (TmVar name)
            _ -> pure (TmApp name args)
      Z.Z3_VAR_AST -> do
        i <- Z.getIndexValue t
        case IntMap.lookup (IntMap.size env - i - 1) env of
          Nothing -> throwError (ErrReflect ("Invalid index: " ++ show t))
          Just (Arg n _) -> pure (TmVar n)
      Z.Z3_NUMERAL_AST -> do
        ty <- Z.getSort t >>= reflectTy
        reflectIntTy ty t
      _ -> throwError (ErrReflect ("Unsupported type: " ++ show k))

reflectVal :: (MonadIO m) => EnvFrom -> Z.AST -> SolveT m Val
reflectVal env ast = do
  tm <- reflectTm env ast
  case expVal tm of
    Nothing -> throwError (ErrReflect ("Not value: " ++ show ast))
    Just val -> pure val

defVar :: (MonadIO m) => String -> Ty -> SolveT m ()
defVar name = defFun' RoleVar name []

defVars :: (MonadIO m) => [String] -> Ty -> SolveT m ()
defVars ns ty = traverse_ (`defVar` ty) ns

defConst :: (MonadIO m) => String -> Ty -> SolveT m ()
defConst name = defFun name []

defConsts :: (MonadIO m) => [String] -> Ty -> SolveT m ()
defConsts ns ty = traverse_ (`defConst` ty) ns

defFun :: (MonadIO m) => String -> [(String, Ty)] -> Ty -> SolveT m ()
defFun = defFun' RoleUninterp

defFuns :: (MonadIO m) => [String] -> [(String, Ty)] -> Ty -> SolveT m ()
defFuns ns args ret = traverse_ (\n -> defFun n args ret) ns

defFun' :: (MonadIO m) => Role -> String -> [(String, Ty)] -> Ty -> SolveT m ()
defFun' role name args ret = do
  let tmd = TmDef role args ret
  fd' <- mkFuncDecl name tmd
  setDef name (ZDefTm (ZTmDef tmd fd'))

defTy :: (MonadIO m) => String -> Maybe Ty -> SolveT m ()
defTy name mty = do
  sort' <- getOrCreateSort name mty
  setDef name (ZDefTy (ZTyDef (TyDef mty) sort'))

defTys :: (MonadIO m) => [String] -> Maybe Ty -> SolveT m ()
defTys ns mty = traverse_ (`defTy` mty) ns

data VarErr = VarErr !String !Ty !Ty
  deriving stock (Eq, Ord, Show)

gatherVars :: (MonadIO m) => Tm -> SolveT m (Either VarErr (Map String Ty))
gatherVars tm0 = runExceptT (execStateT (cata go tm0) Map.empty)
 where
  go tm = case tm of
    TmVarF x -> do
      (ZTmDef (TmDef role _ ty) _) <- lift (lift (getTm x))
      case role of
        RoleVar -> do
          mty <- gets (Map.lookup x)
          case mty of
            Nothing -> modify' (Map.insert x ty)
            Just ty' ->
              if ty == ty'
                then pure ()
                else throwError (VarErr x ty ty')
        _ -> pure ()
    _ -> sequence_ tm

mkEnvTo :: Map String Ty -> EnvTo
mkEnvTo = foldl' go Map.empty . zip [0 ..] . Map.toList
 where
  go m (i, (k, ty)) = Map.insert k (Arg i ty) m

mkExplicitForall :: (MonadIO m) => EnvTo -> Tm -> SolveT m Z.AST
mkExplicitForall env e = do
  liftIO (print env)
  e' <- mkTm env e
  if Map.null env
    then pure e'
    else do
      syms' <- traverse Z.mkStringSymbol (Map.keys env)
      sorts' <- traverse (getSort . argTy) (Map.elems env)
      Z.mkForall [] syms' sorts' e'

mkImplicitForall :: (MonadIO m) => Tm -> SolveT m Z.AST
mkImplicitForall e = do
  z <- gatherVars e
  case z of
    Left ve -> throwError (ErrVar ve)
    Right vars -> mkExplicitForall (mkEnvTo vars) e

assert :: (MonadIO m) => Tm -> SolveT m ()
assert tm = do
  x <- mkImplicitForall tm
  liftIO (putStrLn "*** Asserting:")
  y <- Z.astToString x
  liftIO (putStrLn y)
  Z.assert x

assertWith :: (MonadIO m) => [(String, Ty)] -> Tm -> SolveT m ()
assertWith vars tm = do
  x <- mkExplicitForall (mkEnvTo (Map.fromList vars)) tm
  liftIO (putStrLn "*** Asserting:")
  y <- Z.astToString x
  liftIO (putStrLn y)
  Z.assert x

check :: (MonadIO m) => SolveT m Z.Result
check = Z.check

data FuncEntry = FuncEntry
  { feArgs :: ![Val]
  , feValue :: !Val
  }
  deriving stock (Eq, Ord, Show)

reflectFuncEntry :: (MonadIO m) => EnvFrom -> Z.FuncEntry -> SolveT m FuncEntry
reflectFuncEntry env fe = do
  numArgs <- Z.funcEntryGetNumArgs fe
  args <- traverse (Z.funcEntryGetArg fe >=> reflectVal env) [0 .. numArgs - 1]
  value <- Z.funcEntryGetValue fe >>= reflectVal env
  pure (FuncEntry args value)

data FuncInterp = FuncInterp
  { fiArgNames :: ![String]
  , fiEntries :: ![FuncEntry]
  , fiElseCase :: !(Maybe Tm)
  }
  deriving stock (Eq, Ord, Show)

reflectFuncInterp :: (MonadIO m) => [String] -> EnvFrom -> Z.FuncInterp -> SolveT m FuncInterp
reflectFuncInterp names env fi = do
  numEntries <- Z.funcInterpGetNumEntries fi
  entries <- traverse (Z.funcInterpGetEntry fi >=> reflectFuncEntry env) [0 .. numEntries - 1]
  ec' <- Z.funcInterpGetElse fi
  ecKind' <- Z.getAstKind ec'
  ec <- case ecKind' of
    Z.Z3_UNKNOWN_AST -> pure Nothing
    _ -> fmap Just (reflectTm env ec')
  pure (FuncInterp names entries ec)

data Interp = InterpConst !Tm | InterpFunc !FuncInterp
  deriving stock (Eq, Ord, Show)

type Model = Map String Interp

reflectMod :: (MonadIO m) => Z.Model -> SolveT m Model
reflectMod m = do
  numConsts <- Z.numConsts m
  o1 <-
    if numConsts == 0
      then pure Map.empty
      else foldM' Map.empty [0 .. numConsts - 1] $ \o i -> do
        x <- Z.getConstDecl m i
        my <- Z.getConstInterp m x
        case my of
          Nothing -> pure o
          Just y -> do
            name <- Z.getDeclName x >>= Z.getSymbolString
            z <- reflectTm IntMap.empty y
            pure (Map.insert name (InterpConst z) o)
  numFuncs <- Z.numFuncs m
  if numFuncs == 0
    then pure o1
    else foldM' o1 [0 .. numFuncs - 1] $ \o i -> do
      x <- Z.getFuncDecl m i
      my <- Z.getFuncInterp m x
      case my of
        Nothing -> pure o
        Just y -> do
          name <- Z.getDeclName x >>= Z.getSymbolString
          (names, env) <- mkEnvFrom name
          z <- reflectFuncInterp names env y
          pure (Map.insert name (InterpFunc z) o)

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

valSameTy :: Val -> Val -> Bool
valSameTy (ValBool _) (ValBool _) = True
valSameTy (ValInt ty1 _) (ValInt ty2 _) = ty1 == ty2
valSameTy _ _ = False

guardValSameTy :: (MonadError String m) => Val -> Val -> m ()
guardValSameTy v1 v2 =
  unless
    (valSameTy v1 v1)
    (throwError ("Val tys differ: " ++ show v1 ++ " " ++ show v2))

valAsBool :: (MonadError String m) => Val -> m Bool
valAsBool = \case
  ValBool b -> pure b
  v -> throwError ("Not bool: " ++ show v)

addVals :: [String] -> [Val] -> Map String Val -> Map String Val
addVals names vs m0 = foldl' (\m (n, v) -> Map.insert n v m) m0 (zip names vs)

interp :: Model -> Tm -> Either String Val
interp m = runExcept . flip runReaderT Map.empty . goTop
 where
  goTop :: Tm -> ReaderT (Map String Val) (Except String) Val
  goTop = cata (sequence >=> goRec)
  goRec :: TmF Val -> ReaderT (Map String Val) (Except String) Val
  goRec = \case
    TmVarF n -> do
      mv <- asks (Map.lookup n)
      case mv of
        Just v -> pure v
        Nothing -> case Map.lookup n m of
          Just (InterpConst tm) -> goTop tm
          _ -> throwError ("Var not found: " ++ n)
    TmAppF n vs -> do
      case Map.lookup n m of
        Just (InterpFunc (FuncInterp names entries mec)) -> do
          unless (length names == length vs) $
            throwError ("Bad app arity for " ++ n)
          case find (\(FuncEntry ws _) -> ws == vs) entries of
            Just (FuncEntry _ v) -> pure v
            Nothing -> case mec of
              Nothing -> throwError ("Func entry not found for " ++ n)
              Just ec -> local (addVals names vs) (goTop ec)
        _ -> throwError ("Func not found: " ++ n)
    TmBoolF b -> pure (ValBool b)
    TmIntF ty i -> pure (ValInt ty i)
    TmEqF v1 v2 -> ValBool (v1 == v2) <$ guardValSameTy v1 v2
    TmLtF v1 v2 -> ValBool (v1 < v2) <$ guardValSameTy v1 v2
    TmNotF v -> fmap (ValBool . not) (valAsBool v)
    TmIteF v1 v2 v3 -> fmap (\b1 -> if b1 then v2 else v3) (valAsBool v1)
    TmIffF v1 v2 -> liftA2 (\b1 b2 -> ValBool (b1 == b2)) (valAsBool v1) (valAsBool v2)
    TmImpliesF v1 v2 -> liftA2 (\b1 b2 -> ValBool (not b1 || b2)) (valAsBool v1) (valAsBool v2)
    TmAndF vs -> fmap ValBool (andAllM valAsBool vs)
    TmOrF vs -> fmap ValBool (orAllM valAsBool vs)
    TmXorF _ _ -> undefined
    TmDistinctF _ -> undefined
