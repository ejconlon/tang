module Tang.Test where

import PropUnit (TestTree, testGroup, testMain, testUnit, (===))
import Tang.Test.Search (testSearch)

testDummy :: TestTree
testDummy = testUnit "dummy" $ do
  let actual = (1 + 1) :: Int
      expected = 2 :: Int
  actual === expected

main :: IO ()
main = testMain $ \_ ->
  testGroup
    "Tang"
    [ testDummy
    , testSearch
    ]
