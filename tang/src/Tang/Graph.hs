{-# LANGUAGE UndecidableInstances #-}

-- | Unification graphs
module Tang.Graph
  ( IxPath
  , IxPathSet
  , newPaths
  , WithPaths (..)
  , MetaVar (..)
  , MetaWithPaths
  , Elem (..)
  , elemPaths
  , elemTraversal
  , Graph
  , ResErr (..)
  , resolveVar
  )
where

import Control.Exception (Exception)
import Control.Monad.Except (Except, MonadError (..), runExcept)
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Control.Monad.State.Strict (MonadState (..), StateT (..), evalStateT, gets, modify')
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

newtype MetaVar = MetaVar {unMetaVar :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

type IxPath = Seq Int

-- a trie would be better
type IxPathSet = NESet IxPath

newPaths :: IxPath -> IxPathSet
newPaths = NESet.singleton

data WithPaths a = WithPaths !IxPathSet !a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type MetaWithPaths = WithPaths MetaVar

data Elem f
  = ElemNode !IxPathSet !(f MetaVar)
  | ElemMeta !IxPathSet

elemPaths :: Elem f -> IxPathSet
elemPaths = \case
  ElemNode ips _ -> ips
  ElemMeta ips -> ips

deriving stock instance (Eq (f MetaVar)) => Eq (Elem f)

deriving stock instance (Ord (f MetaVar)) => Ord (Elem f)

deriving stock instance (Show (f MetaVar)) => Show (Elem f)

elemTraversal :: (Traversable f) => Traversal' (Elem f) MetaVar
elemTraversal = traversalVL $ \g -> \case
  ElemNode ips fb -> fmap (ElemNode ips) (traverse g fb)
  ElemMeta ips -> pure (ElemMeta ips)

type Graph f = IntLikeMap MetaVar (Elem f)

-- When resolving, the graph is constant, and we maintain a scoped path
-- to detect cycles.
data ResEnv f = ResEnv
  { reGraph :: !(Graph f)
  , reSeen :: !(IntLikeSet MetaVar)
  }

-- | Resolution can go wrong in many ways...
data ResErr
  = ResErrLoop !MetaWithPaths
  | ResErrNotFound !MetaVar
  | ResErrUnsolvedMeta !MetaWithPaths
  deriving stock (Eq, Show)

instance Exception ResErr

type ResGraph u = IntLikeMap MetaVar u

newtype ResM f u a = ResM {unResM :: ReaderT (ResEnv f) (StateT (ResGraph u) (Except ResErr)) a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (ResEnv f), MonadState (ResGraph u), MonadError ResErr)

runResM :: ResM f u a -> Graph f -> Either ResErr a
runResM m gr = runExcept (evalStateT (runReaderT (unResM m) (ResEnv gr ILS.empty)) ILM.empty)

-- Resolve a type by meta var.
resolveVarM :: (Corecursive u, Base u ~ f, Traversable f) => MetaVar -> ResM f u u
resolveVarM v = do
  minf <- gets (ILM.lookup v)
  case minf of
    Just u -> pure u
    Nothing -> do
      ResEnv m seen <- ask
      case ILM.lookup v m of
        Nothing -> throwError (ResErrNotFound v)
        Just j -> do
          let ips = elemPaths j
              mwp = WithPaths ips v
          if ILS.member v seen
            then throwError (ResErrLoop mwp)
            else do
              u <- case j of
                ElemNode _ x -> local (\re -> re {reSeen = ILS.insert v (reSeen re)}) (resolveNodeM x)
                ElemMeta _ -> throwError (ResErrUnsolvedMeta mwp)
              modify' (ILM.insert v u)
              pure u

-- Resolve a type by node.
resolveNodeM :: (Corecursive u, Base u ~ f, Traversable f) => f MetaVar -> ResM f u u
resolveNodeM n = fmap embed (traverse resolveVarM n)

-- | Resolve a type by meta var.
resolveVar :: (Corecursive u, Base u ~ f, Traversable f) => MetaVar -> Graph f -> Either ResErr u
resolveVar = runResM . resolveVarM
