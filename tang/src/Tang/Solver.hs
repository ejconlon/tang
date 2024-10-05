module Tang.Solver
  ( Result (..)
  , ModelResult (..)
  , Solver
  , Checker
  )
where

import Tang.PropDef (Assignment)

-- | Better than a Bool - is the problem sat or unsat?
data Result
  = ResultSat
  | ResultUnsat
  deriving stock (Eq, Show)

-- | Result with model
data ModelResult a
  = ModelResultSat !a
  | ModelResultUnsat
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

type Solver f v x = f v -> IO (ModelResult (Assignment x))

type Checker f v = f v -> IO Result
