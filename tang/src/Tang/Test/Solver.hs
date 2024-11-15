{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver (testSolver) where

import PropUnit (TestTree, testUnit, (===))
import Tang.Exp (Exp (..))
import Tang.Solver (Sort (..), query, relation, rule, solve)
import Z3.Base qualified as Z

testSolver :: TestTree
testSolver = testUnit "solver" $ do
  (resBefore, resAfter) <- solve $ do
    relation "a" [] SortBool
    relation "b" [] SortBool
    relation "c" [] SortBool
    rule (ExpImplies "b" "a")
    rule (ExpImplies "c" "b")
    resBefore <- query ["a"]
    rule "c"
    resAfter <- query ["a"]
    pure (resBefore, resAfter)
  resBefore === Z.Unsat
  resAfter === Z.Sat
