-- | Backtracking search.
module Tang.Search
  ( SearchT
  , SearchM
  , searchAll
  , searchN
  , search1
  , interleaveApplySeq
  , interleaveSeq
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad.Except (ExceptT (..), MonadError, runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Logic (LogicT, MonadLogic (..), observeAllT, observeManyT)
import Control.Monad.Reader (MonadReader, ReaderT (..))
import Control.Monad.State.Strict (MonadState, StateT (..))
import Data.Functor ((<&>))
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq

newtype SearchT e r s m a = SearchT {unSearchT :: ReaderT r (ExceptT e (StateT s (LogicT m))) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError e, MonadReader r, MonadState s)

type SearchM e r s = SearchT e r s Identity

-- private
unwrap :: SearchT e r s m a -> r -> s -> LogicT m (Either e a, s)
unwrap m r = runStateT (runExceptT (runReaderT (unSearchT m) r))

-- private
wrap :: (r -> s -> LogicT m (Either e a, s)) -> SearchT e r s m a
wrap f = SearchT (ReaderT (ExceptT . StateT . f))

instance Alternative (SearchT e r s m) where
  empty = wrap (\_ _ -> empty)
  x <|> y = wrap (\r s -> unwrap x r s <|> unwrap y r s)

instance (Monad m) => MonadLogic (SearchT e r s m) where
  msplit x =
    let f = unwrap x
    in  wrap $ \r s0 -> do
          z <- msplit (f r s0)
          case z of
            Nothing -> empty
            Just ((ea, s1), tl) ->
              case ea of
                Left e -> pure (Left e, s1)
                Right a -> pure (Right (Just (a, wrap (\_ _ -> tl))), s1)
  interleave x y = wrap (\r s -> interleave (unwrap x r s) (unwrap y r s))

searchAll :: (Monad m) => SearchT e r s m a -> r -> s -> m [(Either e a, s)]
searchAll m r s = observeAllT (unwrap m r s)

searchN :: (Monad m) => Int -> SearchT e r s m a -> r -> s -> m [(Either e a, s)]
searchN n m r s = observeManyT n (unwrap m r s)

search1 :: (Monad m) => SearchT e r s m a -> r -> s -> m (Maybe (Either e a, s))
search1 m r s =
  searchN 1 m r s <&> \case
    [] -> Nothing
    z : _ -> Just z

interleaveApplySeq :: (Monad m) => (x -> SearchT e r s m a) -> Seq x -> SearchT e r s m a
interleaveApplySeq f = go
 where
  go = \case
    Empty -> empty
    m :<| Empty -> f m
    s ->
      let (s1, s2) = Seq.splitAt (div (Seq.length s) 2) s
      in  interleave (go s1) (go s2)

interleaveSeq :: (Monad m) => Seq (SearchT e r s m a) -> SearchT e r s m a
interleaveSeq = interleaveApplySeq id
