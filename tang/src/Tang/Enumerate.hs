{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Applicative (Alternative, empty)
import Control.Exception (Exception)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (state)
import Data.Foldable (foldl')
import IntLike.Map qualified as ILM
import Optics (lens)
import Tang.Ecta
import Tang.Search (SearchM, interleaveApplySeq)
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
  { esGraph :: !(NodeGraph f c)
  , esNextSid :: !SynthId
  , esUnion :: !(Union f)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens esGraph (\x y -> x {esGraph = y})

data EnumErr
  = EnumErrNodeMissing !NodeId
  | EnumErrEtc
  deriving stock (Eq, Ord, Show)

instance Exception EnumErr

type EnumM f c = SearchM EnumErr (EnumSt f c)

-- private
foldLastM :: (Foldable f, Alternative m) => (x -> m a) -> f x -> m a
foldLastM f = foldl' (\ma x -> ma *> f x) empty

enumerate :: NodeGraph f Con -> EnumM f c SynthId
enumerate (NodeGraph r _ nm _) = goStart r
 where
  goStart a = freshId >>= flip goContinue a
  goContinue b a = do
    n <- findNode a
    handleNode b n
  findNode a = maybe (throwError (EnumErrNodeMissing a)) pure (ILM.lookup a nm)
  freshId = state (\es -> let sx = es.esNextSid in (sx, es {esNextSid = succ sx}))
  handleNode b = \case
    NodeSymbol _ -> error "TODO enumerate symbol"
    NodeUnion xs -> interleaveApplySeq (goContinue b) xs
    NodeIntersect xs -> foldLastM (goContinue b) xs
    NodeClone _ -> error "TODO enumerate clone"
