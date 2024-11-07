{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Exception (Exception)
import Control.Monad.Except (ExceptT, throwError)
import Control.Monad.State.Strict (StateT, modify', runStateT, state)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (runExceptT)
import Data.Sequence (Seq (..))
import Data.Set (Set)
import Data.Typeable (Typeable)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Lens', equality', lens)
import Tang.Align (Alignable, alignWithM)
import Tang.Ecta
import Tang.Search (SearchM, interleaveApplySeq)
import Tang.UnionMap (UnionMap)
import Tang.UnionMap qualified as UM
import Tang.Util (foldLastM)

newtype SynthId = SynthId {unSynthId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

data NodeElem f c = NodeElem
  { neChildren :: !(Seq SynthId)
  , neStructure :: !(f ChildIx)
  , neConstraints :: !(Set c)
  }

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (NodeElem f c)

deriving stock instance (Ord c, Ord (f ChildIx)) => Ord (NodeElem f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (NodeElem f c)

data Elem f c
  = ElemMeta
  | ElemNode !(NodeElem f c)

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (Elem f c)

deriving stock instance (Ord c, Ord (f ChildIx)) => Ord (Elem f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (Elem f c)

data ElemInfo f c = ElemInfo
  { eiNodes :: !(IntLikeSet NodeId)
  , eiElem :: !(Elem f c)
  }

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (ElemInfo f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (ElemInfo f c)

newtype SynEqCon = SynEqCon {unSynEqCon :: IntLikeSet SynthId}
  deriving stock (Eq, Ord, Show)

type AlignT e f c m = StateT (Seq SynEqCon) (ExceptT e m)

runAlignT :: AlignT e f c m a -> Seq SynEqCon -> m (Either e (a, Seq SynEqCon))
runAlignT m = runExceptT . runStateT m

alignNodeElem :: (Alignable e f, Monad m) => NodeElem f c -> NodeElem f c -> AlignT e f c m (NodeElem f c)
alignNodeElem = error "TODO"

alignElemInfo :: (Alignable e f, Monad m) => ElemInfo f c -> ElemInfo f c -> AlignT e f c m (ElemInfo f c)
alignElemInfo = goStart
 where
  goStart (ElemInfo n1 e1) (ElemInfo n2 e2) =
    fmap (ElemInfo (ILS.union n1 n2)) (goAlign e1 e2)
  goAlign e1 = \case
    ElemMeta -> pure e1
    e2@(ElemNode n2) -> case e1 of
      ElemMeta -> pure e2
      ElemNode n1 -> fmap ElemNode (alignNodeElem n1 n2)

data Union f c = Union
  { unionNextSid :: !SynthId
  , unionNodes :: !(IntLikeMap NodeId SynthId)
  , unionElems :: !(UnionMap SynthId (ElemInfo f c))
  }

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (Union f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (Union f c)

class HasUnion f c s | s -> f where
  unionL :: Lens' s (Union f c)

instance HasUnion f c (Union f c) where
  unionL = equality'

data EnumSt f c = EnumSt
  { esGraph :: !(NodeGraph f c)
  , esUnion :: !(Union f c)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens esGraph (\x y -> x {esGraph = y})

instance HasUnion f c (EnumSt f c) where
  unionL = lens esUnion (\x y -> x {esUnion = y})

data EnumErr e
  = EnumErrNodeMissing !NodeId
  | EnumErrEmbed !NodeId !e
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (EnumErr e)

type EnumM e f c = SearchM (EnumErr e) (EnumSt f c)

enumerate :: (Alignable e f) => NodeGraph f IxEqCon -> EnumM e f c SynthId
enumerate (NodeGraph r nm _) = goStart r
 where
  goStart = error "TODO"

-- goStart a = freshId >>= flip goContinue a
-- goContinue b a = do
--   n <- findNode a
--   handleNode a b n
-- findNode a = maybe (throwError (EnumErrNodeMissing a)) pure (ILM.lookup a nm)
-- findOrig a = maybe (throwError (EnumErrNodeMissing a)) pure (ILM.lookup a om)
-- freshId = state $ \es ->
--   let sx = es.esNextSid
--       union' =
--         case UM.add sx ElemMeta es.esUnion of
--           UM.AddResAdded u -> u
--           UM.AddResDuplicate -> error "impossible"
--   in (sx, es {esNextSid = succ sx, esUnion = union'})
-- addDefaultMeta sx = modify' $ \es ->
--   let union' =
--         case UM.add sx ElemMeta es.esUnion of
--           UM.AddResAdded u -> u
--           UM.AddResDuplicate -> error "impossible"
--   in (es {esNextSid = succ sx, esUnion = union'})
-- handleNode a b = \case
--   NodeSymbol (SymbolNode _cs _si) -> do
--
--     o <- findOrig a
--
--     error "TODO enumerate symbol"
--   NodeUnion xs -> interleaveApplySeq (goContinue b) xs
--   NodeIntersect xs -> foldLastM (goContinue b) xs
--   NodeClone _nid -> error "TODO enumerate clone"
