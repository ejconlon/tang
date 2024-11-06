{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Exception (Exception)
import Optics (Traversal', lens, traversed)
import Tang.Ecta
import Tang.Search (SearchM)
import Tang.UnionMap (UnionMap)

newtype Fix f = Fix {unFix :: f (Fix f)}

deriving stock instance (Eq (f (Fix f))) => Eq (Fix f)

deriving stock instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

newtype SynthId = SynthId {unSynthId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

data Elem f r
  = ElemMeta
  | ElemNode !(f r)
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq r, Eq (f r)) => Eq (Elem f r)

deriving stock instance (Ord r, Ord (f r)) => Ord (Elem f r)

deriving stock instance (Show r, Show (f r)) => Show (Elem f r)

type Union f = UnionMap SynthId (Elem f SynthId)

data EnumSt f c = EnumSt
  { bsGraph :: !(NodeGraph f c)
  , bsNextSid :: !SynthId
  , bsUnion :: !(Union f)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens bsGraph (\x y -> x {bsGraph = y})

data EnumErr
  = EnumErrNodeMissing !NodeId
  | EnumErrEtc
  deriving stock (Eq, Ord, Show)

instance Exception EnumErr

type EnumM f c = SearchM EnumErr (EnumSt f c)

-- enumerate :: (Traversable f) => NodeGraph f Con -> EnumM f c NodeId
-- enumerate (NodeGraph r nm _) = go r
--  where
--   go a = case ILM.lookup a nm of
--     Nothing -> throwError (EnumErrNodeMissing a)
--     Just (NodeInfo _ _ _ b) -> case b of
--       NodeSymbol _ -> todo
--       NodeUnion _ -> todo
--       NodeIntersect _ -> todo
--       NodeClone _ -> todo
