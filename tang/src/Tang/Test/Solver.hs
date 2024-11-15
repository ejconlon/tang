{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Exp (Exp (..))
import Tang.Solver (SolveM, Sort (..), answer, assertions, newSolveSt, query, relation, rule, solve)
import Z3.Base qualified as Z

testSolver :: TestTree
testSolver =
  testGroup
    "solver"
    [ testRules1
    , testRules2
    ]

exampleRules1 :: SolveM ()
exampleRules1 = do
  relation "a" [] SortBool
  relation "b" [] SortBool
  relation "c" [] SortBool
  rule (ExpImplies "b" "a")
  rule (ExpImplies "c" "b")

testRules1 :: TestTree
testRules1 = testUnit "rules1" $ do
  ss <- newSolveSt
  resBefore <- solve ss $ do
    exampleRules1
    query ["a"]
  resBefore === Z.Unsat
  resAfter <- solve ss $ do
    rule "c"
    query ["a"]
  resAfter === Z.Sat
  ans <- solve ss answer
  ans === ExpBool True
  ass <- solve ss assertions
  ass === []

exampleRules2 :: SolveM ()
exampleRules2 = do
  pure ()

testRules2 :: TestTree
testRules2 = testUnit "rules2" $ do
  ss <- newSolveSt
  solve ss exampleRules2
