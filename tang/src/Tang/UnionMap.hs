-- | (Import this module qualified)
module Tang.UnionMap
  ( Changed (..)
  , maybeChanged
  , Equiv (..)
  , emptyEquiv
  , Entry (..)
  , filterRootEntries
  , MergeOne
  , MergeMany
  , adaptMergeOne
  , foldMergeOne
  , foldMergeMany
  , concatMergeOne
  , concatMergeMany
  , UnionMap (unUnionMap)
  , UnionMapLens
  , empty
  , size
  , member
  , toList
  , values
  , AddRes (..)
  , AddVal (..)
  , add
  , addLM
  , addM
  , TraceRes (..)
  , trace
  , LookupRes (..)
  , LookupVal (..)
  , lookup
  , lookupLM
  , lookupM
  , equiv
  , equivLM
  , equivM
  , compact
  , compactLM
  , compactM
  , canonicalize
  , canonicalizeLM
  , canonicalizeM
  , UpdateRes (..)
  , UpdateVal (..)
  , update
  , updateLM
  , updateM
  , MergeRes (..)
  , MergeVal (..)
  , mergeOne
  , mergeOneLM
  , mergeOneM
  , mergeMany
  , mergeManyLM
  , mergeManyM
  , extract
  , extractLM
  , extractM
  )
where

import Control.Monad.Except (Except, MonadError (..), runExcept)
import Control.Monad.State.Strict (MonadState, StateT, get, put, runStateT, state)
import Data.Coerce (Coercible)
import Data.Foldable (fold, foldl')
import Data.Foldable qualified as F
import Data.Maybe (fromMaybe, mapMaybe)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Lens', Traversal', equality', over, set, view)
import Prelude hiding (lookup)

-- Private util

mayStateLens :: (MonadState s m) => Lens' s x -> (x -> (a, Maybe x)) -> m a
mayStateLens l f = state $ \s ->
  let u = view l s
      (a, mu') = f u
  in  case mu' of
        Nothing -> (a, s)
        Just u' ->
          let s' = set l u' s
          in  (a, s')

stateLens :: (MonadState s m) => Lens' s x -> (x -> (a, x)) -> m a
stateLens l f = state $ \s ->
  let u = view l s
      (a, u') = f u
      s' = set l u' s
  in  (a, s')

newtype DropM e s a = DropM {unDropM :: StateT s (Except e) a}
  deriving newtype (Functor, Applicative, Monad, MonadState s, MonadError e)

runDropM :: DropM e s a -> s -> Either e (a, s)
runDropM it s = runExcept (runStateT (unDropM it) s)

safeTail :: [a] -> [a]
safeTail xs =
  case xs of
    [] -> xs
    _ : ys -> ys

-- The real stuff

data Changed
  = ChangedYes
  | ChangedNo
  deriving stock (Eq, Show)

maybeChanged :: Maybe a -> Changed
maybeChanged = \case
  Nothing -> ChangedNo
  Just _ -> ChangedYes

data Equiv k = Equiv
  { equivFwd :: !(IntLikeMap k (IntLikeSet k))
  , equivBwd :: !(IntLikeMap k k)
  }
  deriving stock (Eq, Show)

emptyEquiv :: Equiv k
emptyEquiv = Equiv ILM.empty ILM.empty

data Entry k v
  = EntryLink !k
  | EntryValue !v
  deriving stock (Eq, Show, Ord, Functor, Foldable, Traversable)

filterRootEntries :: (Coercible k Int) => IntLikeMap k (Entry k v) -> IntLikeMap k v
filterRootEntries = ILM.fromList . mapMaybe (uncurry go) . ILM.toList
 where
  go k = \case
    EntryLink _ -> Nothing
    EntryValue v -> Just (k, v)

type MergeOne e v r = Maybe v -> v -> Either e (r, v)

type MergeMany f e v r = Maybe v -> f v -> Either e (r, v)

adaptMergeOne :: (v -> f v) -> MergeMany f e v r -> MergeOne e v r
adaptMergeOne h g mv = g mv . h

foldMergeOne :: (Monoid r) => (v -> v -> Either e (r, v)) -> MergeOne e v r
foldMergeOne g mv v =
  case mv of
    Nothing -> Right (mempty, v)
    Just w -> g w v

foldMergeMany :: (Foldable f, Monoid r) => Either e v -> (v -> v -> Either e (r, v)) -> MergeMany f e v r
foldMergeMany onE g mv fv = start
 where
  start =
    let vs = F.toList fv
    in  case maybe vs (: vs) mv of
          [] -> fmap (mempty,) onE
          y : ys -> go mempty y ys
  go !r !v = \case
    [] -> Right (r, v)
    w : ws ->
      case g v w of
        Right (s, u) -> go (r <> s) u ws
        e@(Left _) -> e

concatMergeOne :: (Semigroup v) => MergeOne e v ()
concatMergeOne mv v = Right ((), maybe v (<> v) mv)

concatMergeMany :: (Foldable f, Monoid v) => MergeMany f e v ()
concatMergeMany mv vs = concatMergeOne mv (fold vs)

newtype UnionMap k v = UnionMap {unUnionMap :: IntLikeMap k (Entry k v)}
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

type UnionMapLens s k v = Lens' s (UnionMap k v)

empty :: UnionMap k v
empty = UnionMap ILM.empty

size :: UnionMap k v -> Int
size = ILM.size . unUnionMap

member :: (Coercible k Int) => k -> UnionMap k v -> Bool
member k = ILM.member k . unUnionMap

toList :: (Coercible k Int) => UnionMap k v -> [(k, Entry k v)]
toList = ILM.toList . unUnionMap

values :: (Coercible k Int) => UnionMap k v -> IntLikeMap k v
values = foldl' go ILM.empty . toList
 where
  go m (k, ue) =
    case ue of
      EntryValue v -> ILM.insert k v m
      _ -> m

data AddRes k v
  = AddResAdded !(UnionMap k v)
  | AddResDuplicate
  deriving stock (Eq, Show)

add :: (Coercible k Int) => k -> v -> UnionMap k v -> AddRes k v
add k v (UnionMap m) =
  case ILM.lookup k m of
    Nothing -> AddResAdded (UnionMap (ILM.insert k (EntryValue v) m))
    Just _ -> AddResDuplicate

data AddVal
  = AddValAdded
  | AddValDuplicate
  deriving stock (Eq, Show)

addLM :: (Coercible k Int, MonadState s m) => UnionMapLens s k v -> k -> v -> m AddVal
addLM l k v = mayStateLens l $ \u ->
  case add k v u of
    AddResAdded w -> (AddValAdded, Just w)
    AddResDuplicate -> (AddValDuplicate, Nothing)

addM :: (Coercible k Int, MonadState (UnionMap k v) m) => k -> v -> m AddVal
addM = addLM equality'

data TraceRes k v
  = TraceResMissing !k
  | TraceResFound !k !v ![k]
  deriving stock (Eq, Show)

trace :: (Coercible k Int) => k -> UnionMap k v -> TraceRes k v
trace k (UnionMap m) = go [] k
 where
  go !acc j =
    case ILM.lookup j m of
      Nothing -> TraceResMissing j
      Just link -> case link of
        EntryLink kx -> go (j : acc) kx
        EntryValue v -> TraceResFound j v acc

data LookupRes k v
  = LookupResMissing !k
  | LookupResFound !k !v !(Maybe (UnionMap k v))
  deriving stock (Eq, Show)

lookup :: (Coercible k Int) => k -> UnionMap k v -> LookupRes k v
lookup k u = case trace k u of
  TraceResMissing kx -> LookupResMissing kx
  TraceResFound kr vr acc ->
    let mu =
          if null acc
            then Nothing
            else Just (foldl' (\(UnionMap n) kx -> UnionMap (ILM.insert kx (EntryLink kr) n)) u (safeTail acc))
    in  LookupResFound kr vr mu

data LookupVal k v
  = LookupValMissing !k
  | LookupValOk !k !v !Changed
  deriving stock (Eq, Show)

lookupLM :: (Coercible k Int, MonadState s m) => UnionMapLens s k v -> k -> m (LookupVal k v)
lookupLM l k = mayStateLens l $ \u ->
  case lookup k u of
    LookupResMissing x -> (LookupValMissing x, Nothing)
    LookupResFound x y mw -> (LookupValOk x y (maybeChanged mw), mw)

lookupM :: (Coercible k Int, MonadState (UnionMap k v) m) => k -> m (LookupVal k v)
lookupM = lookupLM equality'

equiv :: (Coercible k Int) => UnionMap k v -> (Equiv k, Maybe (UnionMap k v))
equiv u = foldl' go (emptyEquiv, Nothing) (toList u)
 where
  go (Equiv fwd bwd, mw) (k, ue) =
    case ue of
      EntryValue _ ->
        let fwd' = ILM.alter (Just . fromMaybe ILS.empty) k fwd
        in  (Equiv fwd' bwd, mw)
      EntryLink _ ->
        case lookup k (fromMaybe u mw) of
          LookupResMissing _ -> error "impossible"
          LookupResFound r _ mw' ->
            let fwd' = ILM.alter (Just . maybe (ILS.singleton k) (ILS.insert k)) r fwd
                bwd' = ILM.insert k r bwd
            in  (Equiv fwd' bwd', mw')

equivLM :: (Coercible k Int, MonadState s m) => UnionMapLens s k v -> m (Equiv k)
equivLM l = mayStateLens l equiv

equivM :: (Coercible k Int, MonadState (UnionMap k v) m) => m (Equiv k)
equivM = equivLM equality'

-- | Compresses all paths so there is never more than one jump to the root of each class
-- Retains all keys in the map but returns a mapping of non-root -> root keys
compact :: (Coercible k Int) => UnionMap k v -> (IntLikeMap k k, UnionMap k v)
compact u = foldl' go (ILM.empty, u) (toList u)
 where
  go mw@(m, w) (k, ue) =
    if ILM.member k m
      then mw
      else case ue of
        EntryValue _ -> mw
        EntryLink _ ->
          case trace k w of
            TraceResMissing _ -> error "impossible"
            TraceResFound r _ kacc ->
              foldl' (\(m', w') j -> (ILM.insert j r m', UnionMap (ILM.insert j (EntryLink r) (unUnionMap w')))) mw kacc

compactLM :: (Coercible k Int, MonadState s m) => UnionMapLens s k v -> m (IntLikeMap k k)
compactLM l = stateLens l compact

compactM :: (Coercible k Int, MonadState (UnionMap k v) m) => m (IntLikeMap k k)
compactM = compactLM equality'

-- | Compacts and rewrites all values with canonical keys.
-- Retains all keys in the map and again returns a mapping of non-root -> root keys.
-- TODO remove non-canonical keys?
canonicalize :: (Coercible k Int) => Traversal' v k -> UnionMap k v -> (IntLikeMap k k, UnionMap k v)
canonicalize t u = res
 where
  res = let (m, UnionMap w) = compact u in (m, UnionMap (fmap (go m) w))
  go m ue =
    case ue of
      EntryLink _ -> ue
      EntryValue fk -> EntryValue (over t (\j -> ILM.findWithDefault j j m) fk)

canonicalizeLM
  :: (Coercible k Int, MonadState s m) => UnionMapLens s k v -> Traversal' v k -> m (IntLikeMap k k)
canonicalizeLM l t = stateLens l (canonicalize t)

canonicalizeM :: (Coercible k Int, MonadState (UnionMap k v) m) => Traversal' v k -> m (IntLikeMap k k)
canonicalizeM = canonicalizeLM equality'

data UpdateRes e k v r
  = UpdateResMissing !k
  | UpdateResEmbed !e
  | UpdateResAdded !v !r !(UnionMap k v)
  | UpdateResUpdated !k !v !r !(UnionMap k v)
  deriving stock (Eq, Show)

update :: (Coercible k Int, Eq k) => MergeOne e v r -> k -> v -> UnionMap k v -> UpdateRes e k v r
update g k v u@(UnionMap m) = goLookupK
 where
  goLookupK = case lookup k u of
    LookupResMissing kx ->
      if k == kx
        then goAdd
        else UpdateResMissing kx
    LookupResFound kr vr mu -> goMerge kr vr (fromMaybe u mu)
  goAdd =
    case g Nothing v of
      Left e -> UpdateResEmbed e
      Right (r, vg) -> UpdateResAdded vg r (UnionMap (ILM.insert k (EntryValue v) m))
  goMerge kr vr (UnionMap mr) =
    case g (Just vr) v of
      Left e -> UpdateResEmbed e
      Right (r, vg) -> UpdateResUpdated kr vg r (UnionMap (ILM.insert kr (EntryValue vg) mr))

data UpdateVal e k v r
  = UpdateValMissing !k
  | UpdateValEmbed !e
  | UpdateValAdded !v !r
  | UpdateValUpdated !k !v !r
  deriving stock (Eq, Show)

updateLM
  :: (Coercible k Int, Eq k, MonadState s m) => UnionMapLens s k v -> MergeOne e v r -> k -> v -> m (UpdateVal e k v r)
updateLM l g k v = mayStateLens l $ \u ->
  case update g k v u of
    UpdateResMissing x -> (UpdateValMissing x, Nothing)
    UpdateResEmbed e -> (UpdateValEmbed e, Nothing)
    UpdateResAdded y r w -> (UpdateValAdded y r, Just w)
    UpdateResUpdated x y r w -> (UpdateValUpdated x y r, Just w)

updateM :: (Coercible k Int, Eq k, MonadState (UnionMap k v) m) => MergeOne e v r -> k -> v -> m (UpdateVal e k v r)
updateM = updateLM equality'

data MergeRes e k v r
  = MergeResMissing !k
  | MergeResEmbed !e
  | MergeResMerged !k !v !r !(UnionMap k v)
  deriving stock (Eq, Show)

mergeOne :: (Coercible k Int, Eq k) => MergeOne e v r -> k -> k -> UnionMap k v -> MergeRes e k v r
mergeOne g k j u = goLookupK
 where
  doCompactCheck kr jr w jacc = doCompact kr w (if kr == jr then safeTail jacc else jr : jacc)
  doCompact kr w acc = UnionMap (foldl' (\m x -> ILM.insert x (EntryLink kr) m) (unUnionMap w) acc)
  doRoot kr gv w = UnionMap (ILM.insert kr (EntryValue gv) (unUnionMap w))
  goLookupK = case lookup k u of
    LookupResMissing kx -> if k == kx then goAssign else MergeResMissing kx
    LookupResFound kr kv mw -> goLookupJ kr kv (fromMaybe u mw)
  goAssign = case trace j u of
    TraceResMissing jx -> MergeResMissing jx
    TraceResFound jr jv jacc -> goMerge k Nothing jv (doCompactCheck k jr u jacc)
  goLookupJ kr kv w = case trace j w of
    TraceResMissing jx -> MergeResMissing jx
    TraceResFound jr jv jacc -> goMerge kr (Just kv) jv (doCompactCheck kr jr w jacc)
  goMerge kr mkv jv w1 =
    case g mkv jv of
      Left e -> MergeResEmbed e
      Right (r, gv) ->
        let w2 = doRoot kr gv w1
        in  MergeResMerged kr gv r w2

data MergeVal e k v r
  = MergeValMissing !k
  | MergeValEmbed !e
  | MergeValMerged !k !v !r
  deriving stock (Eq, Show)

mergeOneLM
  :: (Coercible k Int, Eq k, MonadState s m) => UnionMapLens s k v -> MergeOne e v r -> k -> k -> m (MergeVal e k v r)
mergeOneLM l g k j = mayStateLens l $ \u ->
  case mergeOne g k j u of
    MergeResMissing x -> (MergeValMissing x, Nothing)
    MergeResEmbed e -> (MergeValEmbed e, Nothing)
    MergeResMerged x y r w -> (MergeValMerged x y r, Just w)

mergeOneM :: (Coercible k Int, Eq k, MonadState (UnionMap k v) m) => MergeOne e v r -> k -> k -> m (MergeVal e k v r)
mergeOneM = mergeOneLM equality'

mergeMany :: (Traversable f, Coercible k Int, Eq k) => MergeMany f e v r -> k -> f k -> UnionMap k v -> MergeRes e k v r
mergeMany g k js u = goLookupK
 where
  doCompactCheck kr jr w jacc = doCompact kr w (if kr == jr then safeTail jacc else jr : jacc)
  doCompact kr w acc = UnionMap (foldl' (\m x -> ILM.insert x (EntryLink kr) m) (unUnionMap w) acc)
  doRoot kr gv w = UnionMap (ILM.insert kr (EntryValue gv) (unUnionMap w))
  doTraceJ kr y = do
    w <- get
    case trace y w of
      TraceResMissing jx -> throwError jx
      TraceResFound jr jv jacc -> do
        put (doCompactCheck kr jr w jacc)
        pure jv
  doTraceJs kr = runDropM (traverse (doTraceJ kr) js)
  goLookupK = case lookup k u of
    LookupResMissing kx -> if k == kx then goAssign else MergeResMissing kx
    LookupResFound kr kv mw -> goLookupJs kr kv (fromMaybe u mw)
  goAssign =
    case doTraceJs k u of
      Left jx -> MergeResMissing jx
      Right (jvs, w1) -> goMerge k Nothing jvs w1
  goLookupJs kr kv w =
    case doTraceJs kr w of
      Left jx -> MergeResMissing jx
      Right (jvs, w1) -> goMerge kr (Just kv) jvs w1
  goMerge kr mkv jvs w1 =
    case g mkv jvs of
      Left e -> MergeResEmbed e
      Right (r, gv) ->
        let w2 = doRoot kr gv w1
        in  MergeResMerged kr gv r w2

mergeManyLM
  :: (Traversable f, Coercible k Int, Eq k, MonadState s m)
  => UnionMapLens s k v
  -> MergeMany f e v r
  -> k
  -> f k
  -> m (MergeVal e k v r)
mergeManyLM l g k js = mayStateLens l $ \u ->
  case mergeMany g k js u of
    MergeResMissing x -> (MergeValMissing x, Nothing)
    MergeResEmbed e -> (MergeValEmbed e, Nothing)
    MergeResMerged x y r w -> (MergeValMerged x y r, Just w)

mergeManyM
  :: (Traversable f, Coercible k Int, Eq k, MonadState (UnionMap k v) m)
  => MergeMany f e v r
  -> k
  -> f k
  -> m (MergeVal e k v r)
mergeManyM = mergeManyLM equality'

-- | Return the subgraph accessible from a given key.
extract :: (Coercible k Int) => Traversal' v k -> k -> UnionMap k v -> (Maybe (k, IntLikeMap k v), UnionMap k v)
extract t k0 u =
  let (m, w) = canonicalize t u
      n = filterRootEntries (unUnionMap w)
      mk1 = case ILM.lookup k0 m of
        Nothing -> k0 <$ ILM.lookup k0 n
        Just k1 -> Just k1
      mp = fmap (,n) mk1
  in  (mp, w)

extractLM
  :: (Coercible k Int, MonadState s m)
  => UnionMapLens s k v
  -> Traversal' v k
  -> k
  -> m (Maybe (k, IntLikeMap k v))
extractLM l t k = stateLens l (extract t k)

extractM
  :: (Coercible k Int, MonadState (UnionMap k v) m)
  => Traversal' v k
  -> k
  -> m (Maybe (k, IntLikeMap k v))
extractM = extractLM equality'
