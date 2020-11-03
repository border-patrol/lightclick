||| Borrowed From Idris2 and improved with Test.Unit
module Main

import System
import System.Directory
import System.Clock

import Data.List

import Golden

%default total

tests : List String
tests = [ "000-mux-check"
        , "001-nice-exempler"
        , "002-unused-port"
        , "003-linear-check"
        , "004-malformed-file"
        , "005-locallink"
        , "006-unused-port"
        , "007-firewall"
        , "008-core-alliance-swerv-eh1"
        , "009-scrubbing"
        ]

covering
main : IO ()
main = do args <- getArgs
          case options args of
            Nothing =>  do {fail (usage "lightclick")}
            Just opts => do Just cwd <- currentDir | _ => fail "Unable to get cwd"
                            printLn cwd
                            let tests' = if isNil (onlyNames opts)
                                          then tests
                                          else intersect (onlyNames opts) tests
                            case tests' of
                              Nil => fail "No tests found"
                              (t::ts) => do results <- traverse (runTest opts cwd) (t::ts)
                                            if any not results
                                             then exitWith (ExitFailure 1)
                                             else exitWith ExitSuccess

-- [ EOF ]
