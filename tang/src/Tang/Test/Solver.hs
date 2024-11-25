{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Solver where

import Data.Map.Strict qualified as Map
import PropUnit (PropertyT, TestTree, testGroup, testUnit, (===))
import Tang.Exp (Tm (..), Ty (..), Val (..), tmBv)
import Tang.Solver
  ( Interp (..)
  , assert
  , check
  , defConst
  , defFun
  , defFuns
  , defTy
  , defVars
  , interp
  , model
  , newSolveSt
  , solve
  )
import Z3.Base qualified as Z

testSolver :: TestTree
testSolver =
  testGroup
    "solver"
    [ testSolve1
    , testSolve2
    , testInterp
    ]

testSolve1 :: TestTree
testSolve1 = testUnit "solve1" $ do
  ss <- newSolveSt
  mm <- solve ss $ do
    defConst "a" TyBool
    defConst "b" TyBool
    defConst "c" TyBool
    assert (TmImplies "c" "b")
    assert (TmImplies "b" "a")
    assert "c"
    model
  case mm of
    Just m -> Just (InterpConst (TmBool True)) === Map.lookup "a" m
    Nothing -> fail "expected model"

testSolve2 :: TestTree
testSolve2 = testUnit "rules2" $ do
  let s = tmBv 3
      isTrue t = TmEq t (TmBool True)
      appTrue x ys = isTrue (TmApp x ys)
      modConstEq mm x t = case mm of
        Nothing -> fail "expected model"
        Just m -> Map.lookup x m === Just (InterpConst t)
  ss <- newSolveSt
  res0 <- solve ss $ do
    defTy "s" (Just (TyBv 3))
    defFuns ["edge", "path"] [("vert0", "s"), ("vert1", "s")] TyBool
    defVars ["a", "b", "c"] "s"
    assert $
      TmIff
        (appTrue "path" ["a", "c"])
        ( TmOr
            [ appTrue "edge" ["a", "c"]
            , appTrue "edge" ["c", "a"]
            , TmAnd [appTrue "path" ["a", "b"], appTrue "path" ["b", "c"]]
            ]
        )
    assert (appTrue "edge" [s 1, s 2])
    assert (appTrue "edge" [s 2, s 3])
    assert (appTrue "edge" [s 2, s 4])
    check
  res0 === Z.Sat
  mm1 <- solve ss $ do
    defConst "q1" TyBool
    assert (TmIff (isTrue "q1") (appTrue "path" [s 1, s 4]))
    model
  modConstEq mm1 "q1" (TmBool True)
  mm2 <- solve ss $ do
    defConst "q2" TyBool
    assert (TmIff (isTrue "q2") (appTrue "path" [s 3, s 4]))
    model
  modConstEq mm2 "q2" (TmBool True)
  mm3 <- solve ss $ do
    defFun "q3" [("vert", "s")] TyBool
    assert (TmIff (appTrue "q3" ["b"]) (appTrue "path" [s 1, "b"]))
    defConst "q4" TyBool
    assert (TmIff (isTrue "q4") (appTrue "q3" [s 2]))
    model
  modConstEq mm3 "q4" (TmBool True)

assertLeft :: (Show a) => Either e a -> PropertyT IO ()
assertLeft = \case
  Left _ -> pure ()
  Right a -> fail ("Expected Left, got Right: " ++ show a)

assertRight :: (Show e) => Either e a -> PropertyT IO ()
assertRight = \case
  Left e -> fail ("Expected Left, got Right: " ++ show e)
  Right _ -> pure ()

testInterp :: TestTree
testInterp = testUnit "interp" $ do
  let tmI = TmInt (TyBv 2)
      valI = ValInt (TyBv 2)
      m1 = Map.singleton "x" (InterpConst (tmI 1))
  assertLeft (interp mempty "x")
  interp m1 "x" === Right (valI 1)
  interp m1 (TmLt "x" "x") === Right (ValBool False)
