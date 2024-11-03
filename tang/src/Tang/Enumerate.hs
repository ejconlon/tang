{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Monad.Except (throwError)
import Control.Placeholder (todo)
import Data.Sequence qualified as Seq
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set qualified as ILS
import Optics (Traversal', traversalVL)
import Tang.Ecta
import Tang.Search (SearchM, interleaveSeq)

newtype Fix f = Fix {unFix :: f (Fix f)}

deriving stock instance (Eq (f (Fix f))) => Eq (Fix f)

deriving stock instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

newtype MetaVar = MetaVar {unMetaVar :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

data ElemF f r
  = ElemMeta
  | ElemNode !(f r)
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq r, Eq (f r)) => Eq (ElemF f r)

deriving stock instance (Ord r, Ord (f r)) => Ord (ElemF f r)

deriving stock instance (Show r, Show (f r)) => Show (ElemF f r)

data Elem f = Elem
  { elemKey :: !NodeId
  , elemValue :: !(ElemF f MetaVar)
  }

deriving stock instance (Eq (f MetaVar)) => Eq (Elem f)

deriving stock instance (Ord (f MetaVar)) => Ord (Elem f)

deriving stock instance (Show (f MetaVar)) => Show (Elem f)

elemTraversal :: (Traversable f) => Traversal' (Elem f) MetaVar
elemTraversal = traversalVL (\g (Elem k v) -> fmap (Elem k) (traverse g v))

type Graph f = IntLikeMap MetaVar (Elem f)

data EnumSt f = EnumSt
  { bsNext :: !MetaVar
  , bsGraph :: !(Graph f)
  , bsReverse :: !(IntLikeMap NodeId MetaVar)
  }

type EnumM f = SearchM ResErr (EnumSt f)

enumerate :: (Traversable f) => NodeGraph f (Con ResPath) -> EnumM f (Fix f)
enumerate (NodeGraph r nm _) = go r
 where
  go a = case ILM.lookup a nm of
    Nothing -> throwError (ResErrNodeMissing a)
    Just (NodeInfo _ _ _ b) -> case b of
      NodeSymbol _ -> todo
      NodeChoice ns -> interleaveSeq (Seq.fromList (fmap go (ILS.toList ns)))
      NodeClone _ -> todo
