module Easychair.Structure.Stack
  ( Stack
  , StackF (..)
  , emptyStack
  , nullStack
  , pushStack
  , popStack
  , peekStack
  , revertStack
  , revertMapStack
  , filterStack
  , mapMaybeStack
  ) where

import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))
import GHC.Generics (Generic)

-- | A stack supporting O(1) push, pop, peek, size.
-- Behind the newtype, a "push" onto the stack is implemented as "cons", therefore
-- fold/traverse goes from top of stack to bottom.
newtype Stack a = Stack
  { unStack :: [a]
  } deriving stock (Show, Generic, Traversable)
    deriving newtype (Eq, Functor, Foldable)

-- | The base functor for a stack.
data StackF a b =
    StackNil
  | StackCons !a b
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)

type instance Base (Stack a) = StackF a

instance Recursive (Stack a) where
  project (Stack s) =
    case s of
      [] -> StackNil
      a : s' -> StackCons a (Stack s')

instance Corecursive (Stack a) where
  embed = \case
    StackNil -> Stack []
    StackCons a (Stack s) -> Stack (a : s)

-- | Easy constructor for the empty stack
emptyStack :: Stack a
emptyStack = Stack []

-- | Is the stack empty?
nullStack :: Stack a -> Bool
nullStack = null . unStack

-- | Pushes a an element onto a 'Stack'
pushStack :: a -> Stack a -> Stack a
pushStack a = Stack . (a :) . unStack

-- | Pushes a an element onto a 'Stack'
popStack :: Stack a -> Maybe (a, Stack a)
popStack (Stack s) =
  case s of
    [] -> Nothing
    a : s' -> Just (a, Stack s')

-- | Returns the top element of the stack (most recently pushed).
peekStack :: Stack a -> Maybe a
peekStack (Stack s) =
  case s of
    [] -> Nothing
    a : _ -> Just a

-- | Pops the stack until the popped element matches the predicate.
revertStack :: (a -> Bool) -> Stack a -> Maybe (a, Stack a)
revertStack f = go . unStack where
  go = \case
    [] -> Nothing
    a : s -> if f a then Just (a, Stack s) else go s

-- | Pops the stack until the popped element matches the mapping predicate.
revertMapStack :: (a -> Maybe b) -> Stack a -> Maybe (b, Stack a)
revertMapStack f = go . unStack where
  go = \case
    [] -> Nothing
    a : s ->
      case f a of
        Nothing -> go s
        Just b -> Just (b, Stack s)

-- | Filters contents of the stack
filterStack :: (a -> Bool) -> Stack a -> Stack a
filterStack f = Stack . filter f . unStack

-- | Maps a maybe function over the stack
mapMaybeStack :: (a -> Maybe b) -> Stack a -> Stack b
mapMaybeStack f = Stack . go . unStack where
  go s =
    case s of
      [] -> []
      a : s' ->
        let t = go s'
        in maybe t (: t) (f a)
