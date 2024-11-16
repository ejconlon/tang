{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import Control.Monad.IO.Class (liftIO)
import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Exp (Tm (..), Ty (..), tmBv)
import Tang.Solver (SolveM, answer, assertions, defConst, defRel, defRule, defTy, newSolveSt, query, solve)
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
  defRel "a" []
  defRel "b" []
  defRel "c" []
  defRule (TmImplies "b" "a")
  defRule (TmImplies "c" "b")

testRules1 :: TestTree
testRules1 = testUnit "rules1" $ do
  ss <- newSolveSt
  solve ss exampleRules1
  resBefore <- solve ss $ do
    query ["a"]
  resBefore === Z.Unsat
  resAfter <- solve ss $ do
    defRule "c"
    query ["a"]
  resAfter === Z.Sat
  ans <- solve ss answer
  ans === TmBool True
  ass <- solve ss assertions
  ass === []

exampleRules2 :: SolveM ()
exampleRules2 = do
  let s = tmBv 3
  -- (define-sort s () (_ BitVec 3))
  defTy "s" (Just (TyBv 3))
  -- (declare-rel edge (s s))
  defRel "edge" ["s", "s"]
  -- (declare-rel path (s s))
  defRel "path" ["s", "s"]
  -- (declare-var a s)
  defConst "a" "s"
  -- (declare-var b s)
  defConst "b" "s"
  -- (declare-var c s)
  defConst "c" "s"

  -- (rule (=> (edge a b) (path a b)))
  defRule
    ( TmImplies
        (TmApp "edge" ["a", "b"])
        (TmApp "path" ["a", "b"])
    )
  -- (rule (=> (and (path a b) (path b c)) (path a c)))
  defRule
    ( TmImplies
        (TmAnd [TmApp "path" ["a", "b"], TmApp "path" ["b", "c"]])
        (TmApp "path" ["a", "c"])
    )

  -- (rule (edge #b001 #b010))
  defRule (TmApp "edge" [s 0b001, s 0b010])
  -- (rule (edge #b001 #b011))
  defRule (TmApp "edge" [s 0b001, s 0b011])
  -- (rule (edge #b010 #b100))
  defRule (TmApp "edge" [s 0b010, s 0b100])

  -- (declare-rel q1 ())
  defRel "q1" []
  -- (declare-rel q2 ())
  defRel "q2" []
  -- (declare-rel q3 (s))
  defRel "q3" ["s"]

  -- (rule (=> (path #b001 #b100) q1))
  defRule (TmImplies (TmApp "path" [s 0b001, s 0b100]) "q1")
  -- (rule (=> (path #b011 #b100) q2))
  defRule (TmImplies (TmApp "path" [s 0b011, s 0b100]) "q2")
  -- (rule (=> (path #b001 b) (q3 b)))
  defRule (TmImplies (TmApp "path" [s 0b001, "b"]) (TmApp "q3" ["b"]))

testRules2 :: TestTree
testRules2 = testUnit "rules2" $ do
  ss <- newSolveSt
  solve ss exampleRules2

-- (query q1)
-- (q1, x1) <- solve ss (liftA2 (,) (query ["q1"]) answer)
-- liftIO $ do
--   print q1
--   print x1
-- (query q2)
-- (query q3 :print-answer true)
