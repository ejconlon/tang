{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver (testSolver) where

import PropUnit (TestTree, testUnit, (===))
import Tang.Exp (Exp (..))
import Tang.Solver (Sort (..), newSolveSt, query, relation, rule, solve)
import Z3.Base qualified as Z

testSolver :: TestTree
testSolver = testUnit "solver" $ do
  ss <- newSolveSt
  resBefore <- solve ss $ do
    relation "a" [] SortBool
    relation "b" [] SortBool
    relation "c" [] SortBool
    rule (ExpImplies "b" "a")
    rule (ExpImplies "c" "b")
    query ["a"]
  resBefore === Z.Unsat
  resAfter <- solve ss $ do
    rule "c"
    query ["a"]
  resAfter === Z.Sat
