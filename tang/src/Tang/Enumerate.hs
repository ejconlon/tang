{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Applicative (empty)
import Control.Exception (Exception)
import Control.Monad.Except (ExceptT, MonadError (..), runExcept, throwError)
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
import Tang.Util (foldLastM, stateL, modifyL)
import qualified Data.Sequence as Seq

newtype SynthId = SynthId {unSynthId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

data NodeElem f c = NodeElem
  { neArity :: !Int
  , neStructure :: !(f SynthId)
  , neConstraints :: !(Set c)
  }

deriving stock instance (Eq c, Eq (f SynthId)) => Eq (NodeElem f c)

deriving stock instance (Ord c, Ord (f SynthId)) => Ord (NodeElem f c)

deriving stock instance (Show c, Show (f SynthId)) => Show (NodeElem f c)

data Elem f c
  = ElemMeta
  | ElemNode !(NodeElem f c)

deriving stock instance (Eq c, Eq (f SynthId)) => Eq (Elem f c)

deriving stock instance (Ord c, Ord (f SynthId)) => Ord (Elem f c)

deriving stock instance (Show c, Show (f SynthId)) => Show (Elem f c)

data ElemInfo f c = ElemInfo
  { eiNodes :: !(IntLikeSet NodeId)
  , eiElem :: !(Elem f c)
  }

deriving stock instance (Eq c, Eq (f SynthId)) => Eq (ElemInfo f c)

deriving stock instance (Show c, Show (f SynthId)) => Show (ElemInfo f c)

newtype SynEqCon = SynEqCon {unSynEqCon :: IntLikeSet SynthId}
  deriving stock (Eq, Ord, Show)

data AlignErr e
  = AlignErrEmbed !e
  | AlignErrArity !Int !Int
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (AlignErr e)

type AlignT e f c m = StateT (Seq SynEqCon) (ExceptT (AlignErr e) m)

runAlignT :: AlignT e f c m a -> Seq SynEqCon -> m (Either (AlignErr e) (a, Seq SynEqCon))
runAlignT m = runExceptT . runStateT m

alignNodeElem :: (Alignable e f, Ord c, Monad m) => NodeElem f c -> NodeElem f c -> AlignT e f c m (NodeElem f c)
alignNodeElem (NodeElem a1 f1 c1) (NodeElem a2 f2 c2) =
  if a1 == a2
    then do
      let tellEq s1 s2 = s1 <$ modify' (:|> SynEqCon (ILS.fromList [s1, s2]))
      ef <- runExceptT (alignWithM tellEq f1 f2)
      either (throwError . AlignErrEmbed) (\f3 -> pure (NodeElem a1 f3 (c1 <> c2))) ef
    else throwError (AlignErrArity a1 a2)

alignElemInfo :: (Alignable e f, Ord c, Monad m) => ElemInfo f c -> ElemInfo f c -> AlignT e f c m (ElemInfo f c)
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

deriving stock instance (Eq c, Eq (f SynthId)) => Eq (Union f c)

deriving stock instance (Show c, Show (f SynthId)) => Show (Union f c)

class HasUnion f c s | s -> f c where
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
  | EnumErrAlign !NodeId !(AlignErr e)
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (EnumErr e)

eeNotable :: EnumErr e -> Bool
eeNotable = \case
  EnumErrNodeMissing _ -> True
  EnumErrAlign _ _ -> False

-- Distinguish between "true errors" and those that should just terminate
-- a particular branch of enumeration quietly
guardNotable :: EnumM e f c a -> EnumM e f c a
guardNotable = flip catchError (\e -> if eeNotable e then throwError e else empty)

type EnumM e f c = SearchM (EnumErr e) () (EnumSt f c)

enumerate :: (Alignable e f) => NodeGraph f IxEqCon -> EnumM e f c SynthId
enumerate (NodeGraph root nm _) = goStart root where
  goStart nid = do
    sid <- mkFreshSynthId
    addDefaultMeta sid
    goContinue sid nid
  goContinue sid nid = do
    node <- findNode nid
    handleNode sid nid node
  handleNode sid _nid = \case
    NodeSymbol _ -> error "TODO enum symbol"
    NodeUnion xs -> interleaveApplySeq (goContinue sid) (Seq.fromList (ILS.toList xs))
    NodeIntersect xs -> foldLastM (goContinue sid) (ILS.toList xs)
    NodeClone _nid -> error "TODO enum clone"
  findNode nid = maybe (throwError (EnumErrNodeMissing nid)) pure (ILM.lookup nid nm)
  mkFreshSynthId = stateL unionL $ \u ->
      let sid = u.unionNextSid
      in (sid, u {unionNextSid = succ sid})
  addDefaultMeta sid = modifyL unionL $ \u ->
    let info = ElemInfo ILS.empty ElemMeta
    in case UM.add sid info u.unionElems of
      UM.AddResAdded x -> u { unionElems = x }
      UM.AddResDuplicate -> u
