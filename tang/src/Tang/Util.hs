module Tang.Util where

import Control.Monad (foldM)
import Control.Monad.State.Strict (MonadState, gets, modify')
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Optics (Lens', set, view)

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList

foldM' :: (Foldable f, Monad m) => b -> f a -> (b -> a -> m b) -> m b
foldM' b fa f = foldM f b fa

runStateLens :: (MonadState s m) => Lens' s a -> (a -> m (b, a)) -> m b
runStateLens l f = do
  a <- gets (view l)
  (b, a') <- f a
  modify' (set l a')
  pure b

execStateLens :: (MonadState s m) => Lens' s a -> (a -> m a) -> m ()
execStateLens l f = do
  a <- gets (view l)
  a' <- f a
  modify' (set l a')
