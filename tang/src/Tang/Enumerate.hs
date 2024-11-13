{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Applicative (empty)
import Control.Exception (Exception)
import Control.Monad.Except (MonadError (..), throwError, Except, runExcept)
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
import Data.Tuple (swap)

newtype SynthId = SynthId {unSynthId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

-- data NodeElem f c = NodeElem
--   { neArity :: !Int
--   , neStructure :: !(f SynthId)
--   , neConstraints :: !(Set c)
--   }
--
-- deriving stock instance (Eq c, Eq (f SynthId)) => Eq (NodeElem f c)
--
-- deriving stock instance (Ord c, Ord (f SynthId)) => Ord (NodeElem f c)
--
-- deriving stock instance (Show c, Show (f SynthId)) => Show (NodeElem f c)

data Elem f
  = ElemMeta
  | ElemNode !(f SynthId)

deriving stock instance (Eq (f SynthId)) => Eq (Elem f)

deriving stock instance (Ord (f SynthId)) => Ord (Elem f)

deriving stock instance (Show (f SynthId)) => Show (Elem f)

data ElemInfo f = ElemInfo
  { eiNodes :: !(IntLikeSet NodeId)
  , eiElem :: !(Elem f)
  }

deriving stock instance (Eq (f SynthId)) => Eq (ElemInfo f)

deriving stock instance (Show (f SynthId)) => Show (ElemInfo f)

data AlignErr e
  = AlignErrEmbed !e
  | AlignErrArity !Int !Int
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (AlignErr e)

type SynEqCon = IntLikeSet SynthId

type AlignM e = StateT (Seq SynEqCon) (Except (AlignErr e))

runAlignM :: AlignM e a -> Seq SynEqCon -> Either (AlignErr e) (a, Seq SynEqCon)
runAlignM m = runExcept . runStateT m

alignElemNode :: (Alignable e f) => f SynthId -> f SynthId -> AlignM e (f SynthId)
alignElemNode f1 f2 = do
  let tellEq s1 s2 = s1 <$ modify' (:|> ILS.fromList [s1, s2])
  ef <- runExceptT (alignWithM tellEq f1 f2)
  either (throwError . AlignErrEmbed) pure ef

alignElemInfo :: (Alignable e f) => ElemInfo f -> ElemInfo f -> AlignM e (ElemInfo f)
alignElemInfo = goStart
 where
  goStart (ElemInfo n1 e1) (ElemInfo n2 e2) =
    fmap (ElemInfo (ILS.union n1 n2)) (goAlign e1 e2)
  goAlign e1 = \case
    ElemMeta -> pure e1
    e2@(ElemNode n2) -> case e1 of
      ElemMeta -> pure e2
      ElemNode n1 -> fmap ElemNode (alignElemNode n1 n2)

mergeElemInfo :: (Alignable e f) => UM.MergeOne (AlignErr e) (ElemInfo f) (Seq SynEqCon)
mergeElemInfo = UM.foldMergeOne (\v1 v2 -> fmap swap (runAlignM (alignElemInfo v1 v2) Empty))

data Union f = Union
  { unionNextSid :: !SynthId
  , unionNodes :: !(IntLikeMap NodeId SynthId)
  , unionElems :: !(UnionMap SynthId (ElemInfo f))
  }

deriving stock instance (Eq (f SynthId)) => Eq (Union f)

deriving stock instance (Show (f SynthId)) => Show (Union f)

class HasUnion f s | s -> f where
  unionL :: Lens' s (Union f)

instance HasUnion f (Union f) where
  unionL = equality'

data Susp = Susp !SynthId !EnumEnv
  deriving stock (Eq, Ord, Show)

data EnumSt f c = EnumSt
  { esGraph :: !(NodeGraph f c)
  , esUnion :: !(Union f)
  , esSuspended :: !(IntLikeMap NodeId Susp)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens esGraph (\x y -> x {esGraph = y})

instance HasUnion f (EnumSt f c) where
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
  , eeFrags :: !FragSplit
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

mkFreshMeta :: EnumM e f c SynthId
mkFreshMeta = mkFreshSynth >>= \sid -> sid <$ addDefaultMeta sid where
  -- Draws a fresh metavar
  mkFreshSynth = stateL unionL $ \u ->
    let sid = u.unionNextSid
    in  (sid, u {unionNextSid = succ sid})
  -- Ensures the given id is in the union map
  addDefaultMeta sid = modifyL unionL $ \u ->
    let info = ElemInfo ILS.empty ElemMeta
    in  case UM.add sid info u.unionElems of
          UM.AddResAdded x -> u {unionElems = x}
          UM.AddResDuplicate -> u

lookupOrFreshMeta :: NodeId -> EnumM e f c SynthId
lookupOrFreshMeta nid = do
  msid <- gets (ILM.lookup nid . unionNodes . esUnion)
  maybe mkFreshMeta pure msid

-- Gets the associated elem info (adding meta if not present)
getElemInfo :: SynthId -> EnumM e f c (ElemInfo f)
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
      sid <- mkFreshMeta
      let f1 = Frag p1 sid
          f2 = Frag p2 sid
      go (Set.insert f2 (Set.insert f1 acc)) cons

allFragsSolved :: EnumM e f c Bool
allFragsSolved = goStart
 where
  goStart = do
    FragSplit selfFrags childFrags <- asks eeFrags
    goSelf childFrags (ILS.toList selfFrags)
  goSelf childFrags = \case
    [] -> goChildren (ILM.toList childFrags)
    v : frags -> do
      ElemInfo _ el <- getElemInfo v
      case el of
        ElemMeta -> pure False
        _ -> goSelf childFrags frags
  goChildren = \case
    [] -> pure True
    (_, fs) : rest ->
      goChild rest (toList fs)
  goChild rest = \case
    [] -> goChildren rest
    Frag _ v : frags -> do
      ElemInfo _ el <- getElemInfo v
      case el of
        ElemMeta -> pure False
        _ -> goChild rest frags

insertSymbolNode :: (Alignable e f) => SynthId -> NodeId -> f NodeId -> EnumM e f c (Seq SynEqCon)
insertSymbolNode sid nid struct = do
  struct' <- traverse lookupOrFreshMeta struct
  insertElemNode sid nid struct'

insertElemNode :: (Alignable e f) => SynthId -> NodeId -> f SynthId -> EnumM e f c (Seq SynEqCon)
insertElemNode sid nid ne = do
  u <- gets esUnion
  let info = ElemInfo (ILS.singleton nid) (ElemNode ne)
  (qs, elems') <- case UM.update mergeElemInfo sid info u.unionElems of
    UM.UpdateResMissing _ -> error "impossible"
    UM.UpdateResEmbed e -> asks eePath >>= \p -> throwError (EnumErrAlign p nid e)
    UM.UpdateResAdded _ qs elems' -> pure (qs, elems')
    UM.UpdateResUpdated _ _ qs elems' -> pure (qs, elems')
  modify' (\es -> es { esUnion = u { unionElems = elems' } })
  pure qs

mergeClassesStep :: (Alignable e f) => IntLikeSet SynthId -> EnumM e f c (Seq SynEqCon)
mergeClassesStep = undefined

-- mergeClassesRec

suspend :: SynthId -> NodeId -> EnumM e f c ()
suspend sid nid = do
  env <- ask
  modify' (\es -> es {esSuspended = ILM.insert nid (Susp sid env) es.esSuspended})

enumerate :: (Alignable e f) => NodeId -> EnumM e f IxEqCon SynthId
enumerate = goAllocate
 where
  goAllocate nid = do
    sid <- mkFreshMeta
    goGuarding sid nid
  goGuarding sid nid = do
    -- TODO gather self constraints and apply them here
    -- this may solve fragments and let us avoid suspending
    solved <- allFragsSolved
    if solved
      then goContinue sid nid
      else sid <$ suspend sid nid
  goContinue sid nid = do
    node <- findNode nid
    handleNode sid nid node
  handleNode sid nid = \case
    NodeSymbol sn -> do
      -- Insert symbol node and gather child equalities
      secs <- insertSymbolNode sid nid (snStructure sn)
      -- Merge inherited constraints with new ones
      -- fs1 <- asks (splitFrags . eeFrags)
      -- fs2 <- fmap splitFrags (initFrags (snConstraints sn))
      -- let FragSplit selfIds childFrags = fs1 <> fs2
      -- Apply self constraints
      error "TODO"
      -- Apply child equalities
      error "TODO"
      -- recurse on child nodes (using goGuarded)
      error "TODO"
    NodeUnion xs ->
      interleaveApplySeq (goContinue sid) (Seq.fromList (ILS.toList xs))
    NodeIntersect xs ->
      foldLastM (goContinue sid) (ILS.toList xs)
    NodeClone _xid -> error "TODO enum clone"
