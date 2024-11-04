{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Exception (Exception)
import Control.Monad.Except (throwError)
import Control.Placeholder (todo)
import Data.Sequence qualified as Seq
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set qualified as ILS
import Optics (Traversal', lens, traversed)
import Tang.Ecta
import Tang.Search (SearchM, interleaveSeq)
import Tang.UnionMap (UnionMap)

newtype Fix f = Fix {unFix :: f (Fix f)}

deriving stock instance (Eq (f (Fix f))) => Eq (Fix f)

deriving stock instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

-- newtype MetaVar = MetaVar {unMetaVar :: Int}
--   deriving stock (Show)
--   deriving newtype (Eq, Ord, Enum, Num)

data ElemF f r
  = ElemMeta
  | ElemNode !(f r)
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq r, Eq (f r)) => Eq (ElemF f r)

deriving stock instance (Ord r, Ord (f r)) => Ord (ElemF f r)

deriving stock instance (Show r, Show (f r)) => Show (ElemF f r)

type Elem f = ElemF f NodeId

elemTraversal :: (Traversable f) => Traversal' (Elem f) NodeId
elemTraversal = traversed

type Union f = UnionMap NodeId (Elem f)

data EnumSt f c = EnumSt
  { bsNode :: !(NodeSt f c)
  , bsUnion :: !(Union f)
  }

instance HasNodeSt f c (EnumSt f c) where
  nodeStL = lens bsNode (\x y -> x {bsNode = y})

data EnumErr
  = EnumErrNodeMissing !NodeId
  | EnumErrEtc
  deriving stock (Eq, Ord, Show)

instance Exception EnumErr

type EnumM f c = SearchM EnumErr (EnumSt f c)

enumerate :: (Traversable f) => NodeGraph f (Con Path) -> EnumM f c (Fix f)
enumerate (NodeGraph r nm _) = go r
 where
  go a = case ILM.lookup a nm of
    Nothing -> throwError (EnumErrNodeMissing a)
    Just (NodeInfo _ _ _ b) -> case b of
      NodeSymbol _ -> todo
      NodeChoice ns -> interleaveSeq (Seq.fromList (fmap go (ILS.toList ns)))
      NodeClone _ -> todo
