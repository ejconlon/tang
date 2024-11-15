{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver (testSolver) where

import PropUnit (TestTree, testUnit)
import Tang.Exp (Exp (..))
import Tang.Solver (Sort (..), declareRel, evalM, rule)

testSolver :: TestTree
testSolver = testUnit "solver" $ do
  evalM $ do
    declareRel "a" [] SortBool
    declareRel "b" [] SortBool
    declareRel "c" [] SortBool
    rule (ExpImplies "a" "b")
    rule (ExpImplies "b" "c")
    pure ()
