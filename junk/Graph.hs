{-# LANGUAGE UndecidableInstances #-}

-- | Unification graphs
module Tang.Graph
  -- ( IxPath
  -- , IxPathSet
  -- , newPaths
  -- , WithPaths (..)
  ( MetaVar (..)
  -- , MetaWithPaths
  , Elem (..)
  , elemPaths
  , elemTraversal
  , Graph
  -- , ResErr (..)
  -- , resolveVar
  )
where

import Control.Exception (Exception)
import Control.Monad.Except (Except, MonadError (..), runExcept, ExceptT)
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Control.Monad.State.Strict (MonadState (..), StateT (..), evalStateT, gets, modify', State)
import Data.Functor.Foldable (Base, Corecursive (..))
import Data.Sequence (Seq (..))
import Data.Set.NonEmpty (NESet)
import Data.Set.NonEmpty qualified as NESet
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Traversal', traversalVL)
import Prelude hiding (lookup)
import Control.Placeholder (todo)

newtype MetaVar = MetaVar {unMetaVar :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

-- type IxPath = Seq Int
--
-- -- a trie would be better
-- type IxPathSet = NESet IxPath
--
-- newPaths :: IxPath -> IxPathSet
-- newPaths = NESet.singleton
--
-- data WithPaths a = WithPaths
--   { wpPaths :: !IxPathSet
--   , wpValue :: !a
--   } deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)
--
-- type MetaWithPaths = WithPaths MetaVar

data ElemF n f r
  = ElemMeta
  | ElemNode !(f r)
  | ElemCon !(n r)
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq r, Eq (n r), Eq (f r)) => Eq (ElemF n f r)
deriving stock instance (Ord r, Ord (n r), Ord (f r)) => Ord (ElemF n f r)
deriving stock instance (Show r, Show (n r), Show (f r)) => Show (ElemF n f r)

data Elem k n f = Elem
  { elemKey :: !k
  , elemValue  :: !(ElemF n f MetaVar)
  }

deriving stock instance (Eq k, Eq (n MetaVar), Eq (f MetaVar)) => Eq (Elem k n f)
deriving stock instance (Ord k, Ord (n MetaVar), Ord (f MetaVar)) => Ord (Elem k n f)
deriving stock instance (Show k, Show (n MetaVar), Show (f MetaVar)) => Show (Elem k n f)

elemTraversal :: (Traversable n, Traversable f) => Traversal' (Elem k n f) MetaVar
elemTraversal = traversalVL (\g -> fmap Elem . traverse (traverse g) . unElem)

type Graph k n f = IntLikeMap MetaVar (Elem k n f)

data BuilderSt k n f = BuilderSt
  { bsNext :: !MetaVar
  , bsGraph :: !(Graph k n f)
  , bsReverse :: !(IntLikeMap k MetaVar)
  }

data BuilderErr

type BuilderM k n f = ExceptT BuilderErr (State (BuilderSt k n f))

runBuilderM :: BuilderM k n f a -> BuilderSt k n f -> Either BuilderErr (a, BuilderSt k n f)
runBuilderM = todo

-- newMetaM :: k -> ProcessM e f MetaVar
-- newMetaM ip = declareM (ElemMeta (newPaths ip))
--
-- newNodeM :: IxPath -> f MetaVar -> ProcessM e f MetaVar
-- newNodeM ip fv = declareM (ElemNode (newPaths ip) fv)
--
-- equateM :: (Alignable e f) => MetaVar -> MetaVar -> ProcessM e f ()
-- equateM va vb = do

-- -- When resolving, the graph is constant, and we maintain a scoped path
-- -- to detect cycles.
-- data ResEnv f = ResEnv
--   { reGraph :: !(Graph f)
--   , reSeen :: !(IntLikeSet MetaVar)
--   }
--
-- -- | Resolution can go wrong in many ways...
-- data ResErr
--   = ResErrLoop !MetaWithPaths
--   | ResErrNotFound !MetaVar
--   | ResErrUnsolvedMeta !MetaWithPaths
--   deriving stock (Eq, Show)
--
-- instance Exception ResErr
--
-- type ResGraph u = IntLikeMap MetaVar u
--
-- newtype ResM f u a = ResM {unResM :: ReaderT (ResEnv f) (StateT (ResGraph u) (Except ResErr)) a}
--   deriving newtype (Functor, Applicative, Monad, MonadReader (ResEnv f), MonadState (ResGraph u), MonadError ResErr)
--
-- runResM :: ResM f u a -> Graph f -> Either ResErr a
-- runResM m gr = runExcept (evalStateT (runReaderT (unResM m) (ResEnv gr ILS.empty)) ILM.empty)
--
-- -- Resolve a type by meta var.
-- resolveVarM :: (Corecursive u, Base u ~ f, Traversable f) => MetaVar -> ResM f u u
-- resolveVarM v = do
--   minf <- gets (ILM.lookup v)
--   case minf of
--     Just u -> pure u
--     Nothing -> do
--       ResEnv m seen <- ask
--       case ILM.lookup v m of
--         Nothing -> throwError (ResErrNotFound v)
--         Just j -> do
--           let ips = elemPaths j
--               mwp = WithPaths ips v
--           if ILS.member v seen
--             then throwError (ResErrLoop mwp)
--             else do
--               u <- case j of
--                 ElemNode _ x -> local (\re -> re {reSeen = ILS.insert v (reSeen re)}) (resolveNodeM x)
--                 ElemMeta _ -> throwError (ResErrUnsolvedMeta mwp)
--               modify' (ILM.insert v u)
--               pure u
--
-- -- Resolve a type by node.
-- resolveNodeM :: (Corecursive u, Base u ~ f, Traversable f) => f MetaVar -> ResM f u u
-- resolveNodeM n = fmap embed (traverse resolveVarM n)
--
-- -- | Resolve a type by meta var.
-- resolveVar :: (Corecursive u, Base u ~ f, Traversable f) => MetaVar -> Graph f -> Either ResErr u
-- resolveVar = runResM . resolveVarM
