module Tang.Test.Translate (testTranslate) where

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
  -- res0 === Z.Sat
  pure ()
