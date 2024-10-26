-- | Backtracking search.
module Tang.Search
  ( SearchT
  , SearchM
  , searchN
  , search1
  , interleaveSeq
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad.Except (ExceptT (..), MonadError, runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Logic (LogicT, MonadLogic (..), observeManyT)
import Control.Monad.State.Strict (MonadState, StateT (..))
import Data.Functor ((<&>))
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq

newtype SearchT e s m a = SearchT {unSearchT :: ExceptT e (StateT s (LogicT m)) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError e, MonadState s)

type SearchM e s = SearchT e s Identity

-- private
unwrap :: SearchT e s m a -> s -> LogicT m (Either e a, s)
unwrap = runStateT . runExceptT . unSearchT

-- private
wrap :: (s -> LogicT m (Either e a, s)) -> SearchT e s m a
wrap = SearchT . ExceptT . StateT

instance Alternative (SearchT e s m) where
  empty = wrap (const empty)
  x <|> y = wrap (\s -> unwrap x s <|> unwrap y s)

instance (Monad m) => MonadLogic (SearchT e s m) where
  msplit x =
    let f = unwrap x
    in  wrap $ \s0 -> do
          z <- msplit (f s0)
          case z of
            Nothing -> empty
            Just ((ea, s1), tl) ->
              case ea of
                Left e -> pure (Left e, s1)
                Right a -> pure (Right (Just (a, wrap (const tl))), s1)
  interleave x y = wrap (\s -> interleave (unwrap x s) (unwrap y s))

searchN :: (Monad m) => Int -> SearchT e s m a -> s -> m [(Either e a, s)]
searchN n m s = observeManyT n (unwrap m s)

search1 :: (Monad m) => SearchT e s m a -> s -> m (Maybe (Either e a, s))
search1 m s =
  searchN 1 m s <&> \case
    [] -> Nothing
    z : _ -> Just z

interleaveSeq :: (Monad m) => Seq (SearchT e s m a) -> SearchT e s m a
interleaveSeq = \case
  Empty -> empty
  m :<| Empty -> m
  s ->
    let (s1, s2) = Seq.splitAt (div (Seq.length s) 2) s
    in  interleave (interleaveSeq s1) (interleaveSeq s2)
