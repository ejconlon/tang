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

newtype M a = M {unM :: ReaderT (IORef St) (ExceptT Err Z.Z3) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError Err, Z.MonadZ3)

instance Z.MonadFixedpoint M where
  getFixedpoint = M (lift (lift Z.getFixedpoint))

instance MonadState St M where
  get = M (ask >>= liftIO . readIORef)
  put st = M (ask >>= liftIO . flip writeIORef st)
  state f = M (ask >>= liftIO . flip atomicModifyIORef' (swap . f))

runM :: M a -> St -> Z.Z3 (Either Err a)
runM m st = liftIO (newIORef st) >>= runExceptT . runReaderT (unM m)

evalM :: (MonadIO m) => M a -> m a
evalM m = liftIO (Z.evalZ3 (runM m initSt) >>= either throwIO pure)

stateM :: (St -> M (a, St)) -> M a
stateM f = do
  r <- M ask
  st0 <- liftIO (readIORef r)
  (a, st1) <- f st0
  liftIO (writeIORef r st1)
  pure a

modifyM :: (St -> M St) -> M ()
modifyM f = do
  r <- M ask
  st0 <- liftIO (readIORef r)
  st1 <- f st0
  liftIO (writeIORef r st1)

mkSym :: Sym -> M Z.Symbol
mkSym = \case
  SymNamed n -> Z.mkStringSymbol n
  SymAnon -> stateM $ \st -> do
    let i = st.stNextSym
        st' = st {stNextSym = i + 1}
    x <- Z.mkIntSymbol i
    pure (x, st')

mkSort :: Sort -> M Z.Sort
mkSort = \case
  SortUnint n -> Z.mkStringSymbol n >>= Z.mkUninterpretedSort
  SortBool -> Z.mkBoolSort

mkDecl :: Decl -> M Z.Sort
mkDecl (Decl args ret) = case args of
  [] -> mkSort ret
  _ -> error "TODO"

mkExpF :: ExpF Z.AST -> M Z.AST
mkExpF = \case
  ExpVarF x -> do
    md <- gets (Map.lookup x . stDecls)
    sort' <- case md of
      Nothing -> throwError (ErrMissingDecl x)
      Just d -> mkDecl d
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

mkExp :: Exp -> M Z.AST
mkExp = cata (sequence >=> mkExpF)

declareRel :: String -> [Sort] -> Sort -> M ()
declareRel name args ty = do
  name' <- mkSym (SymNamed name)
  args' <- traverse mkSort args
  ty' <- mkSort ty
  fd <- Z.mkFuncDecl name' args' ty'
  modifyM $ \st ->
    case Map.lookup name st.stDecls of
      Nothing ->
        let decls = Map.insert name (Decl args ty) st.stDecls
        in  pure st {stDecls = decls}
      Just _ -> throwError (ErrDupeDecl name)
  Z.fixedpointRegisterRelation fd

rule :: Exp -> M ()
rule e = do
  e' <- mkExp e
  s' <- mkSym SymAnon
  Z.fixedpointAddRule e' s'
