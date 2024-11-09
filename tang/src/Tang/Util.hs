module Tang.Util where

import Control.Applicative (Alternative (..))
import Control.Monad (foldM)
import Control.Monad.State.Strict (MonadState (..), evalStateT, gets, modify')
import Control.Monad.Trans (lift)
import Data.Foldable (foldl', toList, traverse_)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Optics (Lens', set, view, over)

data IxPair z = IxPair !Int !z
  deriving stock (Functor)

-- Cribbed from indexed-traversable but made strict
newtype IxM m a = IxM {unIxM :: Int -> IxPair (m a)}
  deriving stock (Functor)

instance (Applicative m) => Applicative (IxM m) where
  pure a = IxM (\i -> IxPair i (pure a))
  IxM x <*> IxM y = IxM $ \i ->
    let IxPair _ xx = x i
        IxPair j yy = y i
    in  IxPair j (xx <*> yy)
  liftA2 f (IxM x) (IxM y) = IxM $ \i ->
    let IxPair _ xx = x i
        IxPair j yy = y i
    in  IxPair j (liftA2 f xx yy)

traverseWithIndex :: (Traversable f, Applicative m) => (Int -> a -> m b) -> f a -> m (f b)
traverseWithIndex f s =
  let g a = IxM (\i -> IxPair (i + 1) (f i a))
      t = traverse g s
      IxPair _ mfb = unIxM t 0
  in  mfb

traverseWithIndex_ :: (Foldable f, Applicative m) => (Int -> a -> m ()) -> f a -> m ()
traverseWithIndex_ f s =
  let g a = IxM (\i -> IxPair (i + 1) (f i a))
      t = traverse_ g s
      IxPair _ mu = unIxM t 0
  in  mu

forWithIndex :: (Traversable f, Applicative m) => f a -> (Int -> a -> m b) -> m (f b)
forWithIndex = flip traverseWithIndex

forWithIndex_ :: (Foldable f, Applicative m) => f a -> (Int -> a -> m ()) -> m ()
forWithIndex_ = flip traverseWithIndex_

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList

foldM' :: (Foldable f, Monad m) => b -> f a -> (b -> a -> m b) -> m b
foldM' b fa f = foldM f b fa

foldLastM :: (Foldable f, Alternative m) => (x -> m a) -> f x -> m a
foldLastM f = foldl' (\ma x -> ma *> f x) empty

stateL :: (MonadState s m) => Lens' s a -> (a -> (b, a)) -> m b
stateL l f = state $ \s ->
  let a = view l s
      (b, a') = f a
      s' = set l a' s
  in (b, s')

stateML :: (MonadState s m) => Lens' s a -> (a -> m (b, a)) -> m b
stateML l f = do
  a <- gets (view l)
  (b, a') <- f a
  modify' (set l a')
  pure b

modifyL :: (MonadState s m) => Lens' s a -> (a -> a) -> m ()
modifyL l f = modify' (over l f)

modifyML :: (MonadState s m) => Lens' s a -> (a -> m a) -> m ()
modifyML l f = do
  a <- gets (view l)
  a' <- f a
  modify' (set l a')

fuseMapM :: (Foldable f, Monad m) => (c -> b -> c) -> c -> (a -> m b) -> f a -> m c
fuseMapM update acc0 f = foldM go acc0
 where
  go !acc = fmap (update acc) . f

mapSeqM :: (Foldable f, Monad m) => (a -> m b) -> f a -> m (Seq b)
mapSeqM = fuseMapM (:|>) Empty

mapSetM :: (Foldable f, Monad m, Ord b) => (a -> m b) -> f a -> m (Set b)
mapSetM = fuseMapM (flip Set.insert) Set.empty

zipWithM :: (Traversable f, Monad m) => (a -> b -> m c) -> f a -> f b -> m (f c)
zipWithM f fa fb =
  let lmc0 = zipWith f (toList fa) (toList fb)
  in  flip evalStateT lmc0 $ do
        for fa $ \_ -> do
          lmc <- get
          case lmc of
            [] -> error "impossible"
            mc : lmc' -> do
              put lmc'
              lift mc
