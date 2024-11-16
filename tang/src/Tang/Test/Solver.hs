{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Exp (Tm (..), Ty (..))
import Tang.Solver (SolveM, answer, assertions, newSolveSt, query, relation, rule, solve)
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
  relation "a" [] TyBool
  relation "b" [] TyBool
  relation "c" [] TyBool
  rule (TmImplies "b" "a")
  rule (TmImplies "c" "b")

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
  ans === TmBool True
  ass <- solve ss assertions
  ass === []

exampleRules2 :: SolveM ()
exampleRules2 = do
  -- ;(set-option :fixedpoint.engine datalog)
  -- (define-sort s () (_ BitVec 3))
  -- (declare-rel edge (s s))
  -- (declare-rel path (s s))
  -- (declare-var a s)
  -- (declare-var b s)
  -- (declare-var c s)
  --
  -- (rule (=> (edge a b) (path a b)))
  -- (rule (=> (and (path a b) (path b c)) (path a c)))
  --
  -- (rule (edge #b001 #b010))
  -- (rule (edge #b001 #b011))
  -- (rule (edge #b010 #b100))
  --
  -- (declare-rel q1 ())
  -- (declare-rel q2 ())
  -- (declare-rel q3 (s))
  -- (rule (=> (path #b001 #b100) q1))
  -- (rule (=> (path #b011 #b100) q2))
  -- (rule (=> (path #b001 b) (q3 b)))
  --
  -- (query q1)
  -- (query q2)
  -- (query q3 :print-answer true)

  pure ()

testRules2 :: TestTree
testRules2 = testUnit "rules2" $ do
  ss <- newSolveSt
  solve ss exampleRules2
