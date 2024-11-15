{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import Control.Monad.IO.Class (liftIO)
import PropUnit (TestTree, testUnit, (===))
import Tang.Exp (Exp (..))
import Tang.Solver (SolveM, Sort (..), answer, assertions, newSolveSt, query, relation, rule, solve)
import Z3.Base qualified as Z

exampleRules :: SolveM ()
exampleRules = do
  relation "a" [] SortBool
  relation "b" [] SortBool
  relation "c" [] SortBool
  rule (ExpImplies "b" "a")
  rule (ExpImplies "c" "b")

testSolver :: TestTree
testSolver = testUnit "solver" $ do
  ss <- newSolveSt
  resBefore <- solve ss $ do
    exampleRules
    query ["a"]
  resBefore === Z.Unsat
  resAfter <- solve ss $ do
    rule "c"
    query ["a"]
  resAfter === Z.Sat

-- solve ss answer >>= liftIO . print
-- solve ss assertions >>= liftIO . print
