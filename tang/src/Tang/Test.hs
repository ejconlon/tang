module Tang.Test where

import PropUnit (testGroup, testMain)
import Tang.Test.Dot (testDot)
import Tang.Test.Enumerate (testEnumerate)
import Tang.Test.Search (testSearch)
import Tang.Test.Solver (testSolver)
import Tang.Test.Translate (testTranslate)

main :: IO ()
main = testMain $ \_ ->
  testGroup
    "Tang"
    [ testSearch
    , testEnumerate
    , testDot
    , testSolver
    , testTranslate
    ]
