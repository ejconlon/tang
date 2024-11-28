{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Translate (testTranslate) where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Maybe (fromJust)
import Data.Set qualified as Set
import Data.Text qualified as T
import PropUnit (PropertyT, TestName, TestTree, testGroup, testUnit, (===))
import Tang.Ecta (GraphM, NodeGraph (..), NodeId, SegEqCon)
import Tang.Exp (Tm (..), Ty (..), Val (..))
import Tang.Solver (SolveSt, assert, check, interp, model, newSolveSt, solve)
import Tang.Symbolic (Symbolic (..))
import Tang.Test.Enumerate (buildIxGraph, exampleFx, exampleFxx, exampleFxxyy, exampleX)
import Tang.Translate (extract, stream, streamShow, translate)
import Text.Show.Pretty (pPrint)
import Z3.Monad qualified as Z

type TransGraphM = GraphM Symbolic SegEqCon NodeId

data TransCase = TransCase !TestName !TransGraphM !(SolveSt -> PropertyT IO ())

caseX :: TransCase
caseX = TransCase "X" exampleX (const (pure ()))

caseFx :: TransCase
caseFx = TransCase "Fx" exampleFx (const (pure ()))

caseFxx :: TransCase
caseFxx = TransCase "Fxx" exampleFxx $ \ss -> do
  let f = TmInt (TyBv 2)
      g = ValInt (TyBv 2)
  res1 <- solve ss $ do
    assert $ TmEq "nodeRoot" (f 2)
    assert $ TmEq (f 0) (TmApp "nodeChild" [f 2, f 0])
    assert $ TmEq (f 1) (TmApp "nodeChild" [f 2, f 1])
    assert $ TmEq (f 3) (TmApp "nodeChild" [f 2, f 2])
    check
  res1 === Z.Sat
  m <- fmap fromJust (solve ss model)
  -- liftIO (pPrint m)
  Right (g 0) === interp m (TmApp "nodeChild" [f 2, f 0])
  Right (g 1) === interp m (TmApp "nodeChild" [f 2, f 1])
  Right (g 3) === interp m (TmApp "nodeChild" [f 2, f 2])

caseFxxyy :: TransCase
caseFxxyy = TransCase "Fxxyy" exampleFxxyy (const (pure ()))

testTranslate :: TestTree
testTranslate =
  testGroup
    "translate"
    [ runTransCase caseX
    , runTransCase caseFx
    , runTransCase caseFxx
    , runTransCase caseFxxyy
    , showTransCase caseX ["(x)"]
    , showTransCase caseFx ["(f (x))"]
    , showTransCase caseFxx ["(f (x) (x))"]
    -- , showTransCase caseFxxyy ["(f (x) (x))", "(f (y) (y))"]
    ]

runTransCase :: TransCase -> TestTree
runTransCase (TransCase name graphM act) = testUnit ("run " ++ name) $ do
  (root, graph) <- buildIxGraph graphM
  ss <- newSolveSt
  (dom, res0) <- solve ss $ do
    dom <- translate (ngNodes graph) root
    res0 <- check
    pure (dom, res0)
  solvStr <- solve ss Z.solverToString
  liftIO (putStrLn ("*** Solver:\n" ++ solvStr))
  -- when (res0 == Z.Undef) $ do
  --   unkStr <- solve ss Z.solverGetReasonUnknown
  --   liftIO (putStrLn ("*** Undef reason:\n" ++ unkStr))
  -- when (res0 == Z.Unsat) $ do
  --   core <- solve ss Z.getUnsatCore
  --   if null core
  --     then liftIO (putStrLn "*** No unsat core")
  --     else do
  --       liftIO (putStrLn "*** Unsat core:")
  --       for_ core $ \c -> do
  --         x <- solve ss (Z.astToString c)
  --         liftIO (putStrLn x)
  res0 === Z.Sat
  -- mm <- solve ss model
  -- liftIO (pPrint mm)
  act ss
  mm <- solve ss model
  case mm of
    Just m -> do
      -- liftIO (pPrint graph)
      -- liftIO (pPrint m)
      _xmap <- either fail pure (extract dom m)
      -- liftIO (pPrint xmap)
      -- liftIO (TIO.putStrLn (xmapText xmap))
      pure ()
    Nothing -> pure ()

showTransCase :: TransCase -> [String] -> TestTree
showTransCase (TransCase name graphM _) expectedList = testUnit ("show " ++ name) $ do
  let expectedSet = Set.fromList (fmap T.pack expectedList)
  (root, graph) <- buildIxGraph graphM
  ss <- newSolveSt
  let s0 = stream ss (ngNodes graph) root
  (me, actualSet) <- liftIO (streamShow s0)
  case me of
    Just e -> fail e
    Nothing -> actualSet === expectedSet
