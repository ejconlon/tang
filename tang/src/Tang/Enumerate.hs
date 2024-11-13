{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Applicative (empty)
import Control.Exception (Exception)
import Control.Monad.Except (ExceptT, MonadError (..), throwError)
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT)
import Control.Monad.Trans.Except (runExceptT)
import Data.Foldable (foldl', toList)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
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
import Tang.Util (foldLastM, modifyL, stateL, unionILM)
import Data.Traversable (for)
import Control.Monad.Identity (Identity (..))

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

data AlignErr e
  = AlignErrEmbed !e
  | AlignErrArity !Int !Int
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (AlignErr e)

type SynEqCon = IntLikeSet SynthId

type AlignT e f c m = StateT (Seq SynEqCon) (ExceptT (AlignErr e) m)

runAlignT :: AlignT e f c m a -> Seq SynEqCon -> m (Either (AlignErr e) (a, Seq SynEqCon))
runAlignT m = runExceptT . runStateT m

alignNodeElem :: (Alignable e f, Ord c, Monad m) => NodeElem f c -> NodeElem f c -> AlignT e f c m (NodeElem f c)
alignNodeElem (NodeElem a1 f1 c1) (NodeElem a2 f2 c2) =
  if a1 == a2
    then do
      let tellEq s1 s2 = s1 <$ modify' (:|> ILS.fromList [s1, s2])
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

execAlignM :: AlignT e f c Identity () -> Either (AlignErr e) (Seq SynEqCon)
execAlignM m = fmap snd (runIdentity (runAlignT m Empty))

mergeElemInfo :: (Alignable e f, Ord c) => UM.MergeOne (AlignErr e) (ElemInfo f c) (Seq SynEqCon)
mergeElemInfo = undefined

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

data Susp = Susp !SynthId !EnumEnv
  deriving stock (Eq, Ord, Show)

data EnumSt f c = EnumSt
  { esGraph :: !(NodeGraph f c)
  , esUnion :: !(Union f c)
  , esSuspended :: !(IntLikeMap NodeId Susp)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens esGraph (\x y -> x {esGraph = y})

instance HasUnion f c (EnumSt f c) where
  unionL = lens esUnion (\x y -> x {esUnion = y})

data EnumErr e
  = EnumErrNodeMissing !IxPath !NodeId
  | EnumErrAlign !IxPath !NodeId !(AlignErr e)
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (EnumErr e)

erNotable :: EnumErr e -> Bool
erNotable = \case
  EnumErrNodeMissing {} -> True
  EnumErrAlign {} -> False

-- | Constraint fragment: PEC -> Metavar
data Frag = Frag
  { fragPath :: !IxPath
  , fragVar :: !SynthId
  }
  deriving stock (Eq, Ord, Show)

-- | Split constraint fragment - (Metavar for this node, fragments for children)
data FragSplit = FragSplit !(IntLikeSet SynthId) !(IntLikeMap ChildIx (Set Frag))
  deriving stock (Eq, Ord, Show)

instance Semigroup FragSplit where
  FragSplit x1 y1 <> FragSplit x2 y2 = FragSplit (x1 <> x2) (unionILM y1 y2)

instance Monoid FragSplit where
  mempty = FragSplit ILS.empty ILM.empty

splitFrags :: Set Frag -> FragSplit
splitFrags = foldl' go mempty
 where
  go (FragSplit x y) (Frag p v) = case p of
    Empty -> FragSplit (ILS.insert v x) y
    p0 :<| pN ->
      let z = Frag pN v
      in  FragSplit x (ILM.alter (Just . maybe (Set.singleton z) (Set.insert z)) p0 y)

filterSelfFrags :: Set Frag -> IntLikeSet SynthId
filterSelfFrags = foldl' go ILS.empty
 where
  go x (Frag p v) = case p of
    Empty -> ILS.insert v x
    _ -> x

data EnumEnv = EnumEnv
  { eePath :: !IxPath
  , eeFrags :: !(Set Frag)
  }
  deriving stock (Eq, Ord, Show)

type EnumM e f c = SearchM (EnumErr e) EnumEnv (EnumSt f c)

-- Distinguish between "true errors" and those that should just terminate
-- a particular branch of enumeration quietly
guardNotable :: EnumM e f c a -> EnumM e f c a
guardNotable = flip catchError (\e -> if erNotable e then throwError e else empty)

-- Finds a node by id
findNode :: NodeId -> EnumM e f c (Node f c)
findNode nid = do
  nm <- gets (ngNodes . esGraph)
  maybe (asks eePath >>= \p -> throwError (EnumErrNodeMissing p nid)) pure (ILM.lookup nid nm)

-- Draws a fresh metavar
mkFreshSynthId :: EnumM e f c SynthId
mkFreshSynthId = stateL unionL $ \u ->
  let sid = u.unionNextSid
  in  (sid, u {unionNextSid = succ sid})

-- Ensures the given id is in the union map
addDefaultMeta :: SynthId -> EnumM e f c ()
addDefaultMeta sid = modifyL unionL $ \u ->
  let info = ElemInfo ILS.empty ElemMeta
  in  case UM.add sid info u.unionElems of
        UM.AddResAdded x -> u {unionElems = x}
        UM.AddResDuplicate -> u

mkFreshWithMeta :: EnumM e f c SynthId
mkFreshWithMeta = mkFreshSynthId >>= \sid -> sid <$ addDefaultMeta sid

-- Gets the associated elem info (adding meta if not present)
getElemInfo :: SynthId -> EnumM e f c (ElemInfo f c)
getElemInfo sid = stateL unionL $ \u ->
  case UM.lookup sid u.unionElems of
    UM.LookupResFound _ info mx -> (info, maybe u (\x -> u {unionElems = x}) mx)
    UM.LookupResMissing _ ->
      let info = ElemInfo ILS.empty ElemMeta
      in  case UM.add sid info u.unionElems of
            UM.AddResAdded x -> (info, u {unionElems = x})
            UM.AddResDuplicate -> error "impossible"

initFrags :: Set IxEqCon -> EnumM e f c (Set Frag)
initFrags = go Set.empty . toList where
  go !acc = \case
    [] -> pure acc
    EqCon p1 p2 : cons-> do
      sid <- mkFreshWithMeta
      let f1 = Frag p1 sid
          f2 = Frag p2 sid
      go (Set.insert f2 (Set.insert f1 acc)) cons

allFragsSolved :: EnumM e f c Bool
allFragsSolved = goStart
 where
  goStart = do
    frags <- asks eeFrags
    goEach (toList frags)
  goEach = \case
    [] -> pure True
    Frag _ v : frags -> do
      ElemInfo _ el <- getElemInfo v
      case el of
        ElemMeta -> pure False
        _ -> goEach frags

insertNodeElem :: (Alignable e f, Ord c) => SynthId -> NodeId -> NodeElem f c -> EnumM e f c (Seq SynEqCon)
insertNodeElem sid nid ne = do
  u <- gets esUnion
  let info = ElemInfo (ILS.singleton nid) (ElemNode ne)
  (qs, elems') <- case UM.update mergeElemInfo sid info u.unionElems of
    UM.UpdateResMissing _ -> error "impossible"
    UM.UpdateResEmbed e -> asks eePath >>= \p -> throwError (EnumErrAlign p nid e)
    UM.UpdateResAdded _ qs elems' -> pure (qs, elems')
    UM.UpdateResUpdated _ _ qs elems' -> pure (qs, elems')
  modify' $ \es ->
    let nodes' = ILM.insert nid sid u.unionNodes
        u' = u { unionNodes = nodes', unionElems = elems' }
    in es { esUnion = u' }
  pure qs

suspend :: SynthId -> NodeId -> EnumM e f c ()
suspend sid nid = do
  env <- ask
  modify' (\es -> es {esSuspended = ILM.insert nid (Susp sid env) es.esSuspended})

enumerate :: (Alignable e f) => NodeId -> EnumM e f IxEqCon SynthId
enumerate = goStart
 where
  goStart nid = do
    sid <- mkFreshWithMeta
    goGuarded sid nid
  goGuarded sid nid = do
    solved <- allFragsSolved
    if solved
      then goContinue sid nid
      else sid <$ suspend sid nid
  goContinue sid nid = do
    node <- findNode nid
    handleNode sid nid node
  handleNode sid _nid = \case
    NodeSymbol (SymbolNode _ _ _ _struct _cons) -> do
      -- fs1 <- asks (splitFrags . eeFrags)
      -- fs2 <- fmap splitFrags (initFrags cons)
      -- let FragSplit selfIds childFrags = fs1 <> fs2
      -- struct' <- merge unionIds struct
      -- struct' <- traverse (local update . goStart) struct
      undefined
    NodeUnion xs ->
      interleaveApplySeq (goContinue sid) (Seq.fromList (ILS.toList xs))
    NodeIntersect xs ->
      foldLastM (goContinue sid) (ILS.toList xs)
    NodeClone _xid -> error "TODO enum clone"
