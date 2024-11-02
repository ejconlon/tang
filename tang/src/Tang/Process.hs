{-# LANGUAGE UndecidableInstances #-}

-- | Drives unification by updating a UnionMap
module Tang.Process
  ( RebindMap
  , ProcessErr (..)
  , ProcessState (..)
  , psUnionMapL
  , newProcessState
  , ProcessM
  , runProcessM
  , extract
  -- , MonadUnify (..)
  -- , Unifier
  )
where

import Control.Exception (Exception)
import Control.Monad.Except (Except, ExceptT, MonadError (..), runExcept, runExceptT)
import Control.Monad.State.Strict (MonadState (..), State, StateT, gets, modify', runState, runStateT, state)
import Control.Monad.Writer.Strict (MonadWriter, WriterT, runWriterT, tell)
import Control.Placeholder (todo)
import Data.Foldable (for_)
import Data.Kind (Type)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.These (These (..))
import Data.Traversable (for)
import Data.Typeable (Typeable)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import Optics (lens)
import Tang.Align (Alignable (..))
import Tang.Graph
  ( Elem (..)
  , Graph
  , IxPath
  , MetaVar (..)
  , MetaWithPaths
  , WithPaths (..)
  , elemPaths
  , elemTraversal
  , newPaths
  )
import Tang.UnionMap qualified as UM

type RebindMap = IntLikeMap MetaVar MetaVar

data ProcessErr e
  = ProcessErrDuplicate !MetaVar
  | ProcessErrMissing !MetaVar
  | ProcessErrEmbed !e
  deriving stock (Eq, Ord, Show)

instance (Show e, Typeable e) => Exception (ProcessErr e)

data ProcessState f = ProcessState
  { psUnique :: !MetaVar
  , psUnionMap :: !(UM.UnionMap MetaVar (Elem f))
  }

deriving stock instance (Eq (f MetaVar)) => Eq (ProcessState f)

deriving stock instance (Show (f MetaVar)) => Show (ProcessState f)

psUnionMapL :: UM.UnionMapLens (ProcessState f) MetaVar (Elem f)
psUnionMapL = lens psUnionMap (\ps um -> ps {psUnionMap = um})

newProcessState :: MetaVar -> ProcessState f
newProcessState uniq = ProcessState uniq UM.empty

newtype ProcessM e f a = ProcessM {unProcessM :: ExceptT (ProcessErr e) (State (ProcessState f)) a}
  deriving newtype (Functor, Applicative, Monad, MonadState (ProcessState f), MonadError (ProcessErr e))

runProcessM :: ProcessM e f a -> ProcessState f -> (Either (ProcessErr e) a, ProcessState f)
runProcessM = runState . runExceptT . unProcessM

compactOnState :: ProcessState f -> (RebindMap, ProcessState f)
compactOnState = runState (UM.compactLM psUnionMapL)

canonicalizeOnState :: (Traversable f) => ProcessState f -> (RebindMap, ProcessState f)
canonicalizeOnState = runState (UM.canonicalizeLM psUnionMapL elemTraversal)

extractOnState :: (Traversable f) => ProcessState f -> ((RebindMap, Graph f), ProcessState f)
extractOnState ps = res
 where
  res =
    let (m, ps'@(ProcessState _ u)) = canonicalizeOnState ps
        g = go1 (UM.unUnionMap u)
    in  ((m, g), ps')
  go1 im = fmap (go2 im) im
  go2 im = \case
    -- compaction will have made this a one-link jump
    UM.EntryLink k ->
      case ILM.lookup k im of
        Nothing -> error ("Missing linked key: " ++ show k)
        Just v -> go2 im v
    UM.EntryValue d -> d

-- | Compact the union map - compresses all chains to directly reference roots for faster lookup
-- Returns a map of all rebound (non-root) ids to roots.
compact :: ProcessM e f RebindMap
compact = state compactOnState

-- | Canonicalize the union map - compacts and rewrites nodes identical in structure.
-- Returns a map of all rebound (non-root) ids to roots (include those removed during canonicalization).
canonicalize :: (Traversable f) => ProcessM e f RebindMap
canonicalize = state canonicalizeOnState

-- | Extracts a final graph from the union map, canonicalizing in the process.
extract :: (Traversable f) => ProcessM e f (RebindMap, Graph f)
extract = state extractOnState

lookupP :: MetaVar -> ProcessM e f (MetaVar, Elem f)
lookupP i = do
  val <- UM.lookupLM psUnionMapL i
  case val of
    UM.LookupValMissing x -> throwError (ProcessErrMissing x)
    UM.LookupValOk r d _ -> pure (r, d)

-- data Duo a = Duo !a !a
--   deriving stock (Eq, Show, Functor, Foldable, Traversable)
--
-- data Item = Item
--   { itemChildren :: !(Duo MetaVar)
--   , itemRoot :: !MetaWithPaths
--   }
--   deriving stock (Eq, Show)
--
-- -- Effect used entirely within 'alignMerge'
-- newtype AlignM e f a = AlignM {unAlignM :: WriterT (Seq Item) (StateT MetaVar (Except (ProcessErr e))) a}
--   deriving newtype (Functor, Applicative, Monad, MonadWriter (Seq Item), MonadState MetaVar, MonadError (ProcessErr e))
--
-- runAlignM :: AlignM e f a -> MetaVar -> Either (ProcessErr e) (a, MetaVar, Seq Item)
-- runAlignM al b = fmap (\((a, w), s) -> (a, s, w)) (runExcept (runStateT (runWriterT (unAlignM al)) b))
--
-- alignElems :: (Alignable e f) => Elem f -> Elem f -> AlignM e f (Elem f)
-- alignElems da db =
--   let x = elemPaths da <> elemPaths db
--   in  case da of
--         ElemMeta _ ->
--           case db of
--             ElemMeta _ -> pure (ElemMeta x)
--             ElemNode _ fb -> pure (ElemNode x fb)
--         ElemNode _ fa ->
--           case db of
--             ElemMeta _ -> pure (ElemNode x fa)
--             ElemNode _ fb -> do
--               case align fa fb of
--                 Left e -> throwError (ProcessErrEmbed e)
--                 Right g -> do
--                   fc <- for g $ \these -> do
--                     case these of
--                       This a -> pure a
--                       That b -> pure b
--                       These a b -> do
--                         let duo = Duo a b
--                         root <- state (\i -> (i, succ i))
--                         let item = Item duo (WithPaths x root)
--                         tell (Seq.singleton item)
--                         pure root
--                   pure (ElemNode x fc)
--
-- embedAlignM :: AlignM e f a -> ProcessM e f (a, Seq Item)
-- embedAlignM m = do
--   i <- gets psUnique
--   case runAlignM m i of
--     Left e -> throwError e
--     Right (a, i', its) -> do
--       modify' (\ps -> ps { psUnique = i' })
--       pure (a, its)
--
-- -- -- | Callback to be provided to a union map to merge values of the same key by aligning their structures.
-- -- alignMergeN :: (Alignable e f) => MetaVar -> UM.MergeMany Duo (ProcessErr e) (Elem f) (Seq Item, MetaVar)
-- -- alignMergeN b mdx (Duo di dj) = res
-- --  where
-- --   res = fmap (\(v, s, w) -> ((w, s), v)) (runAlignM body b)
-- --   body = do
-- --     case mdx of
-- --       Just dx -> do
-- --         dy <- alignElems dx di
-- --         alignElems dy dj
-- --       Nothing -> error "impossible"
--
-- -- type MergeOne e v r = Maybe v -> v -> Either e (r, v)
-- -- | Callback to be provided to a union map to merge values of the same key by aligning their structures.
-- alignMerge :: (Alignable e f) => MetaVar -> UM.MergeOne (ProcessErr e) (Elem f) (Seq Item, MetaVar)
-- alignMerge i melA elB =
--   case melA of
--     Nothing -> Right ((Empty, i), elB)
--     Just elA ->
--       fmap (\(elC, i', its) -> ((its, i'), elC)) (runAlignM (alignElems elA elB) i)
--
-- declareM :: Elem f -> ProcessM e f MetaVar
-- declareM el = do
--   ProcessState i m <- get
--   case UM.add i el m of
--     UM.AddResAdded m' -> i <$ put (ProcessState (succ i) m')
--     UM.AddResDuplicate -> throwError (ProcessErrDuplicate i)
--
-- newMetaM :: IxPath -> ProcessM e f MetaVar
-- newMetaM ip = declareM (ElemMeta (newPaths ip))
--
-- newNodeM :: IxPath -> f MetaVar -> ProcessM e f MetaVar
-- newNodeM ip fv = declareM (ElemNode (newPaths ip) fv)
--
-- equateM :: (Alignable e f) => MetaVar -> MetaVar -> ProcessM e f ()
-- equateM va vb = do
--   erb <- UM.mergeOneLM psUnionMapL (alignMerge va vb
--   case erb of
--     UM.MergeValMissing i -> throwError (ProcessErrMissing i)
--     UM.MergeValEmbed e -> throwError e
--     UM.MergeValMerged _ _ () -> pure ()
--
-- class Monad m => MonadUnify f m | m -> f where
--   type UnifyVar m :: Type
--   newMeta :: IxPath -> m (UnifyVar m)
--   newNode :: IxPath -> f (UnifyVar m) -> m (UnifyVar m)
--   equate :: UnifyVar m -> UnifyVar m -> m ()
--
-- instance Alignable e f => MonadUnify f (ProcessM e f) where
--   type UnifyVar (ProcessM e f) = MetaVar
--   newMeta = newMetaM
--   newNode = newNodeM
--   equate = equateM
--
-- type Unifier f = (forall m. (MonadUnify f m) => m ())
