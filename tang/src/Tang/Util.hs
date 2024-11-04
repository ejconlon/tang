module Tang.Util where

import Control.Monad (foldM)
import Control.Monad.State.Strict (MonadState, gets, modify')
import Data.Foldable (toList, traverse_)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Optics (Lens', set, view)

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

forWithIndex_ :: (Traversable f, Applicative m) => f a -> (Int -> a -> m ()) -> m ()
forWithIndex_ = flip traverseWithIndex_

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList

foldM' :: (Foldable f, Monad m) => b -> f a -> (b -> a -> m b) -> m b
foldM' b fa f = foldM f b fa

stateML :: (MonadState s m) => Lens' s a -> (a -> m (b, a)) -> m b
stateML l f = do
  a <- gets (view l)
  (b, a') <- f a
  modify' (set l a')
  pure b

modifyML :: (MonadState s m) => Lens' s a -> (a -> m a) -> m ()
modifyML l f = do
  a <- gets (view l)
  a' <- f a
  modify' (set l a')
