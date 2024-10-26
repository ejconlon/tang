module Tang.Test.Dot (testDot) where

import PropUnit (TestTree, testUnit, (===))

-- import Tang.Dot qualified as TD
-- import Tang.Test.Example qualified as TTE

testDot :: TestTree
testDot = testUnit "dot" $ do
  'x' === 'x'
