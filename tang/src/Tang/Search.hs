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
import Control.Monad.Except (ExceptT (..), MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Logic (LogicT, MonadLogic (..), observeAllT, observeManyT)
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.State.Strict (MonadState (..), StateT (..), gets, modify')
import Data.Functor ((<&>))
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Bifunctor (second)

data SearchSt r s = SearchSt
  { ssEnv :: !r
  , ssSt :: !s
  } deriving stock (Eq, Ord, Show)

newtype SearchT e r s m a = SearchT {unSearchT :: ExceptT e (StateT (SearchSt r s) (LogicT m)) a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError e)

type SearchM e r s = SearchT e r s Identity

instance MonadReader r (SearchT e r s m) where
  ask = SearchT (gets ssEnv)
  local f (SearchT m) = SearchT $ do
    r0 <- state (\ss -> let r0 = ssEnv ss in (r0, ss { ssEnv = f r0 }))
    a <- catchError m $ \e -> do
      modify' (\ss -> ss { ssEnv = r0 })
      throwError e
    a <$ modify' (\ss -> ss { ssEnv = r0 })
  reader f = SearchT (gets (f . ssEnv))

instance MonadState s (SearchT e r s m) where
  get = SearchT (gets ssSt)
  put s = SearchT (modify' (\ss -> ss { ssSt = s }))
  state f = SearchT (state (\ss -> let s0 = ssSt ss in let (a, s1) = f s0 in (a, ss { ssSt = s1 })))

-- private
unwrap :: SearchT e r s m a -> r -> s -> LogicT m (Either e a, s)
unwrap m r s = fmap (second ssSt) (runStateT (runExceptT (unSearchT m)) (SearchSt r s))

-- private
wrap :: (r -> s -> LogicT m (Either e a, s)) -> SearchT e r s m a
wrap f = SearchT (ExceptT (StateT (\(SearchSt r s) -> fmap (second (SearchSt r)) (f r s))))

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
