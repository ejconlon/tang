-- | "Correct" backtracking search.
module Tang.Search
  ( SearchSt (..)
  , ObserveT
  , ObserveM
  , runObserveT
  , runObserveM
  , SearchT
  , SearchM
  , search
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Logic (LogicT, MonadLogic (..), observeManyT)
import Control.Monad.State.Strict (MonadState (..), StateT, gets, modify', runStateT)
import Control.Monad.Trans (MonadTrans (..))
import Data.Bifunctor (second)

-- | Backtracking state - the x component goes forward, the y component backtracks
-- All mentions of state below are really about the backtracking state component.
-- The forward state component is pretty boring.
data SearchSt x y = SearchSt
  { ssFwd :: !x
  , ssBwd :: !y
  }
  deriving stock (Eq, Ord, Show)

-- | Effects used during search: forward and backtracking state, plus whatever
-- else you want to lift in (like errors).
newtype ObserveT x y m a = ObserveT {unObserveT :: StateT (SearchSt x y) m a}
  deriving newtype
    (Functor, Applicative, Monad, MonadState (SearchSt x y), MonadError e, MonadIO, MonadTrans, Alternative)

type ObserveM x y = ObserveT x y Identity

-- | Runs the effects.
runObserveT :: ObserveT x y m a -> SearchSt x y -> m (a, SearchSt x y)
runObserveT = runStateT . unObserveT

runObserveM :: ObserveM x y a -> SearchSt x y -> (a, SearchSt x y)
runObserveM m s = runIdentity (runObserveT m s)

-- | Backtracking search monad. Take care not to expose the constructor!
-- The major issue with backtracking is that the final state is that of
-- the last branch that has executed. In order for the 'msplit' law to hold
-- (`msplit m >>= reflect = m`) we have to ensure that the same state
-- is observable on all exit points. Basically the only way to do this is to
-- not make the state visible at all externally, which requires that we
-- protect the constructor here and only allow elimination of this type
-- with 'observeMany, which resets the state for us.
newtype SearchT x y m a = SearchT {unSearchT :: LogicT (ObserveT x y m) a}
  deriving newtype (Functor, Applicative, Monad, MonadState (SearchSt x y), MonadError e, MonadIO)

type SearchM x y = SearchT x y Identity

instance (Monad m) => Alternative (SearchT x y m) where
  empty = SearchT empty
  x <|> y = do
    saved <- gets ssBwd
    -- Restore the current state before going down the right branch.
    SearchT (unSearchT x <|> unSearchT (restore saved y))

instance (Monad m) => MonadLogic (SearchT x y m) where
  msplit x = SearchT (fmap (fmap (second SearchT)) (msplit (unSearchT x)))
  interleave x y = do
    saved <- gets ssBwd
    -- Again restore the current state before going down the right branch.
    SearchT (interleave (unSearchT x) (unSearchT (restore saved y)))

instance MonadTrans (SearchT x y) where
  lift = SearchT . lift . lift

-- | Wraps logict's 'observeManyT' and forces us to 'reset' the backtracking state.
search :: (Monad m) => Int -> SearchT x y m a -> ObserveT x y m [a]
search n = observeManyT n . unSearchT . reset

-- At many points below we'll need to restore a saved state before
-- continuing the search.
restore :: (Monad m) => y -> SearchT x y m a -> SearchT x y m a
restore saved x = modify' (\st -> st {ssBwd = saved}) *> x

-- Restores the backtracked state after all results have been enumerated.
finalize :: (Monad m) => y -> SearchT x y m a -> SearchT x y m a
finalize saved x = SearchT (unSearchT x <|> unSearchT (restore saved empty))

-- Ensures the backtrack state is returned to the current state.
-- This is run on the outside of the search so the backtracked state is
-- not externally observable.
reset :: (Monad m) => SearchT x y m a -> SearchT x y m a
reset x = do
  saved <- gets ssBwd
  finalize saved x
