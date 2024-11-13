{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Applicative (empty)
import Control.Exception (Exception)
import Control.Monad (unless)
import Control.Monad.Except (Except, MonadError (..), runExcept, throwError)
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT, state)
import Control.Monad.Trans.Except (runExceptT)
import Control.Placeholder (todo)
import Data.Foldable (foldl', for_, toList)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Tuple (swap)
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
import Tang.Util (forWithIndex_, modifyL, stateL, unionILM)

-- | A metavar id used as a key in the union map
newtype SynthId = SynthId {unSynthId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

-- | Solved/unsolved metavar
data Elem f
  = ElemMeta
  | ElemNode !(f SynthId)

deriving stock instance (Eq (f SynthId)) => Eq (Elem f)

deriving stock instance (Ord (f SynthId)) => Ord (Elem f)

deriving stock instance (Show (f SynthId)) => Show (Elem f)

-- | Annotates a metavar with info about what nodes it represents
data ElemInfo f = ElemInfo
  { eiNodes :: !(IntLikeSet NodeId)
  , eiElem :: !(Elem f)
  }

deriving stock instance (Eq (f SynthId)) => Eq (ElemInfo f)

deriving stock instance (Show (f SynthId)) => Show (ElemInfo f)

type SynEqCon = IntLikeSet SynthId

type AlignM e = StateT (Seq SynEqCon) (Except e)

runAlignM :: AlignM e a -> Seq SynEqCon -> Either e (a, Seq SynEqCon)
runAlignM m = runExcept . runStateT m

alignElemNode :: (Alignable e f) => f SynthId -> f SynthId -> AlignM e (f SynthId)
alignElemNode f1 f2 = do
  let tellEq s1 s2 = s1 <$ modify' (:|> ILS.fromList [s1, s2])
  ef <- runExceptT (alignWithM tellEq f1 f2)
  either throwError pure ef

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

mergeElemInfo :: (Alignable e f) => UM.MergeOne e (ElemInfo f) (Seq SynEqCon)
mergeElemInfo = UM.foldMergeOne (\v1 v2 -> fmap swap (runAlignM (alignElemInfo v1 v2) Empty))

data NodeInfo = NodeInfo
  { niPath :: !IxPath
  , niSid :: !SynthId
  }
  deriving stock (Eq, Ord, Show)

data Union f = Union
  { unionNextSid :: !SynthId
  , unionNodes :: !(IntLikeMap NodeId NodeInfo)
  , unionElems :: !(UnionMap SynthId (ElemInfo f))
  }

deriving stock instance (Eq (f SynthId)) => Eq (Union f)

deriving stock instance (Show (f SynthId)) => Show (Union f)

class HasUnion f s | s -> f where
  unionL :: Lens' s (Union f)

instance HasUnion f (Union f) where
  unionL = equality'

data Susp = Susp
  { suspSid :: !SynthId
  , suspEnv :: !EnumEnv
  }
  deriving stock (Eq, Ord, Show)

data EnumSt f c = EnumSt
  { esGraph :: !(NodeGraph f c)
  , esUnion :: !(Union f)
  , esSuspended :: !(IntLikeMap NodeId Susp)
  , esSeen :: !(IntLikeSet NodeId)
  }

instance HasNodeGraph f c (EnumSt f c) where
  nodeGraphL = lens esGraph (\x y -> x {esGraph = y})

instance HasUnion f (EnumSt f c) where
  unionL = lens esUnion (\x y -> x {esUnion = y})

data EnumErr e
  = EnumErrNodeMissing !IxPath !NodeId
  | EnumErrMerge !IxPath !SynthId !SynthId !e
  | EnumErrAlign !IxPath !NodeId !e
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (EnumErr e)

erNotable :: EnumErr e -> Bool
erNotable = \case
  EnumErrNodeMissing {} -> True
  EnumErrMerge {} -> False
  EnumErrAlign {} -> False

-- | Constraint fragment: PEC -> Metavar
data Frag = Frag
  { fragPath :: !IxPath
  , fragVar :: !SynthId
  }
  deriving stock (Eq, Ord, Show)

-- | Split constraint fragment - (Metavar for this node, fragments for children)
data FragSplit = FragSplit
  { fsSelf :: !(IntLikeSet SynthId)
  , fsChildren :: !(IntLikeMap ChildIx (Set Frag))
  }
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

-- Allocate a new metavar - note that you should create metavars associated with nodes
-- only through 'lookupOrFreshMeta'.
mkFreshMeta :: EnumM e f c SynthId
mkFreshMeta = mkFreshSynth >>= \sid -> sid <$ addDefaultMeta sid
 where
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
  minfo <- gets (ILM.lookup nid . unionNodes . esUnion)
  case minfo of
    Just info -> pure (niSid info)
    Nothing -> do
      sid <- mkFreshMeta
      path <- asks eePath
      let info = NodeInfo path sid
      modify' $ \es ->
        let u = es.esUnion
            n = u.unionNodes
            n' = ILM.insert nid info n
            u' = u {unionNodes = n'}
        in  es {esUnion = u'}
      pure sid

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
initFrags = go Set.empty . toList
 where
  go !acc = \case
    [] -> pure acc
    EqCon p1 p2 : cons -> do
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
  modify' (\es -> es {esUnion = u {unionElems = elems'}})
  pure qs

mergeClassesStep :: (Alignable e f) => IntLikeSet SynthId -> EnumM e f c (Seq SynEqCon)
mergeClassesStep = goStart
 where
  goStart xs0 = do
    case ILS.toList xs0 of
      [] -> pure Empty
      x1 : xs -> do
        elems <- gets (unionElems . esUnion)
        (acc, elems') <- goAcc Empty elems x1 xs
        modify' (\es -> es {esUnion = es.esUnion {unionElems = elems'}})
        pure acc
  goAcc !acc !elems !x1 = \case
    [] -> pure (acc, elems)
    (x2 : xs) ->
      case UM.mergeOne mergeElemInfo x1 x2 elems of
        UM.MergeResMissing _ -> error "impossible"
        UM.MergeResEmbed e -> asks eePath >>= \p -> throwError (EnumErrMerge p x1 x2 e)
        UM.MergeResMerged _ _ yss elems' -> goAcc (acc <> yss) elems' x2 xs

mergeClasses :: (Alignable e f) => IntLikeSet SynthId -> EnumM e f c ()
mergeClasses = go . Seq.singleton
 where
  go = \case
    Empty -> pure ()
    xs :<| xss -> do
      yss <- mergeClassesStep xs
      go (yss <> xss)

suspend :: SynthId -> NodeId -> EnumM e f c ()
suspend sid nid = do
  env <- ask
  modify' (\es -> es {esSuspended = ILM.insert nid (Susp sid env) es.esSuspended})

enumerate :: (Alignable e f) => NodeId -> EnumM e f IxEqCon (SynthId, Bool)
enumerate nid = enumStep nid >>= \(sid, _) -> fmap (sid,) enumLoop

enumLoop :: (Alignable e f) => EnumM e f IxEqCon Bool
enumLoop = goStart
 where
  goStart = do
    susp <- state (\es -> (es.esSuspended, es {esSuspended = ILM.empty}))
    if ILM.null susp
      then pure True
      else goLoop False (ILM.toList susp)
  goLoop !progress = \case
    [] -> if progress then goStart else pure False
    (nid, Susp sid env) : rest -> do
      (_, stepProgress) <- local (const env) $ do
        enumStepGuarded sid nid
      goLoop (progress || stepProgress) rest

enumStep :: (Alignable e f) => NodeId -> EnumM e f IxEqCon (SynthId, Bool)
enumStep nid = lookupOrFreshMeta nid >>= \sid -> enumStepGuarded sid nid

enumStepGuarded :: (Alignable e f) => SynthId -> NodeId -> EnumM e f IxEqCon (SynthId, Bool)
enumStepGuarded = goGuarded
 where
  goGuarded sid nid = do
    -- Apply self constraints - this may solve fragments and let us avoid suspending
    FragSplit selfIds childFrags <- asks eeFrags
    mergeClasses selfIds
    -- Update environment
    let frags' = FragSplit ILS.empty childFrags
    local (\ee -> ee {eeFrags = frags'}) $ do
      solved <- allFragsSolved
      if solved
        then do
          hasSeen <- gets (ILS.member nid . esSeen)
          unless hasSeen $ do
            modify' (\es -> es {esSeen = ILS.insert nid es.esSeen})
            goUnguarded sid nid
          pure (sid, True)
        else -- Suspend to wait for more info
          (sid, False) <$ suspend sid nid
  goUnguarded sid nid = do
    node <- findNode nid
    case node of
      NodeSymbol sn -> do
        -- Insert symbol node and gather child equalities
        secs <- insertSymbolNode sid nid (snStructure sn)
        -- Merge inherited constraints with new ones
        fs1 <- asks eeFrags
        fs2 <- fmap splitFrags (initFrags (snConstraints sn))
        let FragSplit selfIds childFrags = fs1 <> fs2
        -- Apply self constraints
        mergeClasses selfIds
        -- Apply child equalities
        for_ secs mergeClasses
        -- recurse on child nodes (guarding for unsolved)
        forWithIndex_ (snStructure sn) $ \ix cnid -> do
          csid <- lookupOrFreshMeta cnid
          let frags = fromMaybe Set.empty (ILM.lookup (ChildIx ix) childFrags)
              cfs = splitFrags frags
          local (\ee -> ee {eeFrags = cfs}) (goGuarded csid cnid)
      NodeUnion xs ->
        -- Interleave results from enumerating union branches
        -- Each branch uses the same sid but state is reset between them
        interleaveApplySeq (goUnguarded sid) (Seq.fromList (ILS.toList xs))
      NodeIntersect xs ->
        -- Merge enumerations of all child branches
        -- Each branch uses the same sid and state is preserved between them
        for_ (ILS.toList xs) (goUnguarded sid)
      NodeClone _xid ->
        -- We must unfold the graph here
        todo
