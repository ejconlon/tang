module Tang.Solver where

import Control.Exception (Exception, throwIO)
import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (..), ask)
import Control.Monad.State.Strict (MonadState (..), gets)
import Control.Monad.Trans (lift)
import Data.Functor.Foldable (cata)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.String (IsString (..))
import Data.Tuple (swap)
import Tang.Exp (Exp (..), ExpF (..))
import Z3.Monad qualified as Z

data Sym = SymNamed !String | SymAnon
  deriving stock (Eq, Ord, Show)

instance IsString Sym where
  fromString = SymNamed

data Sort = SortUnint !String | SortBool
  deriving stock (Eq, Ord, Show)

data Decl = Decl ![Sort] !Sort
  deriving stock (Eq, Ord, Show)

data St = St
  { stNextSym :: !Int
  , stDecls :: !(Map String Decl)
  }
  deriving stock (Eq, Ord, Show)

initSt :: St
initSt = St 0 Map.empty

data Err
  = ErrDupeDecl !String
  | ErrMissingDecl !String
  deriving stock (Eq, Ord, Show)

instance Exception Err

newtype SolveM a = SolveM {unSolveM :: ReaderT (IORef St) (ExceptT Err Z.Z3) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError Err, Z.MonadZ3)

instance Z.MonadFixedpoint SolveM where
  getFixedpoint = SolveM (lift (lift Z.getFixedpoint))

instance MonadState St SolveM where
  get = SolveM (ask >>= liftIO . readIORef)
  put st = SolveM (ask >>= liftIO . flip writeIORef st)
  state f = SolveM (ask >>= liftIO . flip atomicModifyIORef' (swap . f))

runSolveM :: SolveM a -> St -> Z.Z3 (Either Err a)
runSolveM m st = liftIO (newIORef st) >>= runExceptT . runReaderT (unSolveM m)

solve :: (MonadIO m) => SolveM a -> m a
solve m = liftIO (Z.evalZ3 (runSolveM m initSt) >>= either throwIO pure)

getM :: (St -> SolveM a) -> SolveM a
getM f = do
  r <- SolveM ask
  st0 <- liftIO (readIORef r)
  f st0

stateM :: (St -> SolveM (a, St)) -> SolveM a
stateM f = do
  r <- SolveM ask
  st0 <- liftIO (readIORef r)
  (a, st1) <- f st0
  liftIO (writeIORef r st1)
  pure a

modifyM :: (St -> SolveM St) -> SolveM ()
modifyM f = do
  r <- SolveM ask
  st0 <- liftIO (readIORef r)
  st1 <- f st0
  liftIO (writeIORef r st1)

mkSym :: Sym -> SolveM Z.Symbol
mkSym = \case
  SymNamed n -> Z.mkStringSymbol n
  SymAnon -> stateM $ \st -> do
    let i = st.stNextSym
        st' = st {stNextSym = i + 1}
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
    md <- gets (Map.lookup x . stDecls)
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
getDecl name = getM $ \st ->
  case Map.lookup name st.stDecls of
    Nothing -> throwError (ErrMissingDecl name)
    Just d -> pure d

setDecl :: String -> Decl -> SolveM ()
setDecl name decl = modifyM $ \st ->
  case Map.lookup name st.stDecls of
    Nothing ->
      let decls = Map.insert name decl st.stDecls
      in  pure st {stDecls = decls}
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
