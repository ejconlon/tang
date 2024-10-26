module Tang.Test where

import PropUnit (testGroup, testMain)
import Tang.Test.Dot (testDot)
import Tang.Test.Search (testSearch)

main :: IO ()
main = testMain $ \_ ->
  testGroup
    "Tang"
    [ testSearch
    , testDot
    ]
