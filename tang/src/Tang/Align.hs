module Tang.Align where

import Control.Exception (Exception)
import Control.Monad (void)
import Control.Monad.Except (ExceptT, MonadError (..), runExcept, runExceptT)
import Control.Monad.Trans (lift)
import Data.Foldable (toList)
import Data.Typeable (Typeable)
import Tang.Util (zipWithM)

data AlignAllErr e
  = AlignAllErrEmpty
  | AlignAllErrIx !Int !e
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

instance (Show e, Typeable e) => Exception (AlignAllErr e)

-- | Aligns the holes of compatible structures
class (Traversable f) => Alignable e f | f -> e where
  -- | If the two structures are alignable, return a structure filled with shared parts.
  -- Law: A structure must align with itself in the natural way.
  -- Law: Structures must individually align with their successful alignment in the natural way.
  align :: f a -> f b -> Either e (f (a, b))
  align = alignWith (,)

  -- | 'align' but saving you an 'fmap' to eliminate a tuple
  alignWith :: (a -> b -> c) -> f a -> f b -> Either e (f c)
  alignWith f fa fb = runExcept (alignWithM (\a b -> pure (f a b)) fa fb)

  -- | The monadic version
  alignWithM :: (Monad m) => (a -> b -> m c) -> f a -> f b -> ExceptT e m (f c)

  -- | 'align' several things in one go
  alignAll :: (Foldable t) => (a -> z) -> (z -> a -> z) -> t (f a) -> Either (AlignAllErr e) (f z)
  alignAll g f = runExcept . alignAllM (pure . g) (\z a -> pure (f z a))

  -- | The monadic version
  alignAllM :: (Foldable t, Monad m) => (a -> m z) -> (z -> a -> m z) -> t (f a) -> ExceptT (AlignAllErr e) m (f z)
  alignAllM g f = goStart . toList
   where
    goStart = \case
      [] -> throwError AlignAllErrEmpty
      fa : fas -> do
        fz <- lift (traverse g fa)
        goContinue 1 fz fas
    goContinue !i !fz = \case
      [] -> pure fz
      fa : fas -> do
        efz' <- lift (runExceptT (alignWithM f fz fa))
        case efz' of
          Left e -> throwError (AlignAllErrIx i e)
          Right fz' -> goContinue (i + 1) fz' fas

data EqAlignErr = EqAlignErr
  deriving stock (Eq, Ord, Show)

instance Exception EqAlignErr

eqAlignWithM :: (Traversable f, Eq (f ()), Monad m) => (a -> b -> m c) -> f a -> f b -> ExceptT EqAlignErr m (f c)
eqAlignWithM f fa fb =
  if void fa == void fb
    then lift (zipWithM f fa fb)
    else throwError EqAlignErr

newtype ViaEq f a = ViaEq {unViaEq :: f a}
  deriving stock (Functor, Foldable, Traversable)

instance (Traversable f, Eq (f ())) => Alignable EqAlignErr (ViaEq f) where
  alignWithM f (ViaEq fa) (ViaEq fb) = fmap ViaEq (eqAlignWithM f fa fb)
