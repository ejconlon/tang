{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Translate (testTranslate) where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Foldable (for_)
import PropUnit (PropertyT, TestName, TestTree, testGroup, testUnit, (===))
import Tang.Ecta (GraphM, NodeGraph (..), NodeId, SegEqCon)
import Tang.Exp (Tm (..), Ty (..))
import Tang.Solver (SolveSt, assert, check, model, newSolveSt, solve)
import Tang.Symbolic (Symbol (..), Symbolic (..))
import Tang.Test.Enumerate (buildIxGraph, exampleFxx, exampleFxxyy)
import Tang.Translate (translate)
import Text.Show.Pretty (pPrint)
import Z3.Monad qualified as Z

testTranslate :: TestTree
testTranslate =
  testGroup
    "translate"
    [ runTransCase "Fxx" exampleFxx $ \ss -> do
        res1 <- solve ss $ do
          let f = TmInt (TyBv 2)
          assert $ TmEq "nodeRoot" (f 1)
          assert $ TmEq (f 0) (TmApp "nodeChild" [f 1, f 0])
          assert $ TmEq (f 0) (TmApp "nodeChild" [f 1, f 1])
          assert $ TmEq (f 2) (TmApp "nodeChild" [f 1, f 2])
          check
        res1 === Z.Sat
        -- , runTransCase "Fxxyy" exampleFxxyy (const (pure ()))
    ]

runTransCase :: TestName -> GraphM Symbolic SegEqCon NodeId -> (SolveSt -> PropertyT IO ()) -> TestTree
runTransCase name graphM act = testUnit name $ do
  (root, graph) <- buildIxGraph graphM
  ss <- newSolveSt
  res0 <- solve ss $ do
    translate (ngNodes graph) root
    check
  -- TODO fixit
  solvStr <- solve ss Z.solverToString
  liftIO (putStrLn ("*** Solver:\n" ++ solvStr))
  when (res0 == Z.Undef) $ do
    unkStr <- solve ss Z.solverGetReasonUnknown
    liftIO (putStrLn ("*** Undef reason:\n" ++ unkStr))
  when (res0 == Z.Unsat) $ do
    core <- solve ss Z.getUnsatCore
    if null core
      then liftIO (putStrLn "*** No unsat core")
      else do
        liftIO (putStrLn "*** Unsat core:")
        for_ core $ \c -> do
          x <- solve ss (Z.astToString c)
          liftIO (putStrLn x)
  res0 === Z.Sat
  mm <- solve ss model
  liftIO (pPrint mm)
  act ss
