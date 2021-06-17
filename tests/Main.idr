||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

tests : TestPool
tests
  = MkTestPool "Tests"
        []
        [ "000-mux-check"
        , "001-nice-exempler"
        , "002-unused-port"
        , "003-linear-check"
        , "004-malformed-file"
        , "005-locallink"
        , "006-unused-port"
        , "007-firewall"
        , "008-core-alliance-swerv-eh1"
        , "009-scrubbing"
        , "010-gates"
        ]

covering
main : IO ()
main
  = runner [ tests
           ]
-- [ EOF ]
