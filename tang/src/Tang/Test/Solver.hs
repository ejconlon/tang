{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import Data.Set qualified as Set
import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Exp (Tm (..), Ty (..), tmBv)
import Tang.Solver (SolveM, answer, defRel, defRule, defTy, defVar, newSolveSt, query, solve)
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
  defRule "a" ["b"]
  defRule "b" ["c"]

testRules1 :: TestTree
testRules1 = testUnit "rules1" $ do
  ss <- newSolveSt
  solve ss exampleRules1
  resBefore <- solve ss $ do
    query "a"
  resBefore === Z.Unsat
  resAfter <- solve ss $ do
    defRule "c" []
    query "a"
  resAfter === Z.Sat
  ansAfter <- solve ss (answer "a" [])
  ansAfter === Just (TmBool True)

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
  defVar "a" "s"
  -- (declare-var b s)
  defVar "b" "s"
  -- (declare-var c s)
  defVar "c" "s"

  -- (rule (=> (edge a b) (path a b)))
  defRule
    (TmApp "path" ["a", "b"])
    [TmApp "edge" ["a", "b"]]
  -- (rule (=> (and (path a b) (path b c)) (path a c)))
  defRule
    (TmApp "path" ["a", "c"])
    [TmApp "path" ["a", "b"], TmApp "path" ["b", "c"]]

  -- (rule (edge #b001 #b010))
  defRule (TmApp "edge" [s 0b001, s 0b010]) []
  -- (rule (edge #b001 #b011))
  defRule (TmApp "edge" [s 0b001, s 0b011]) []
  -- (rule (edge #b010 #b100))
  defRule (TmApp "edge" [s 0b010, s 0b100]) []

  -- (declare-rel q1 ())
  defRel "q1" []
  -- (declare-rel q2 ())
  defRel "q2" []
  -- (declare-rel q3 (s))
  defRel "q3" ["s"]

  -- (rule (=> (path #b001 #b100) q1))
  defRule "q1" [TmApp "path" [s 0b001, s 0b100]]
  -- (rule (=> (path #b011 #b100) q2))
  defRule "q2" [TmApp "path" [s 0b011, s 0b100]]
  -- (rule (=> (path #b001 b) (q3 b)))
  defRule (TmApp "q3" ["b"]) [TmApp "path" [s 0b001, "b"]]

testRules2 :: TestTree
testRules2 = testUnit "rules2" $ do
  let s = tmBv 3
  ss <- newSolveSt
  solve ss exampleRules2
  -- (query q1)
  (q1, a1) <- solve ss (liftA2 (,) (query "q1") (answer "q1" []))
  q1 === Z.Sat
  a1 === Just (TmBool True)
  -- (query q2)
  (q2, a2) <- solve ss (liftA2 (,) (query "q2") (answer "q2" []))
  q2 === Z.Unsat
  a2 === Nothing
  -- (query q3)
  (q3, a3) <- solve ss (liftA2 (,) (query "q3") (answer "q3" ["b"]))
  q3 === Z.Sat
  -- How consistent is this ordering of solutions?
  -- May need to make this more robust at some point
  let expectedTms = Set.fromList (fmap (TmEq "b" . s) [2, 3, 4])
  case a3 of
    Just (TmOr eqList) -> do
      let actualTms = Set.fromList eqList
      actualTms === expectedTms
    _ -> fail "expected or"
