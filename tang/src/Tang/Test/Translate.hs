module Tang.Test.Translate (testTranslate) where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Foldable (for_)
import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Ecta (NodeGraph (..))
import Tang.Solver (check, newSolveSt, solve)
import Tang.Symbolic (Symbol (..), Symbolic (..))
import Tang.Test.Enumerate (buildIxGraph, exampleFxx, exampleFxxyy)
import Tang.Translate (translate)
import Z3.Monad qualified as Z

testTranslate :: TestTree
testTranslate =
  testGroup
    "translate"
    [ testTransFxx
    ]

testTransFxx :: TestTree
testTransFxx = testUnit "Fxx" $ do
  (root, graph) <- buildIxGraph exampleFxx
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
  pure ()
