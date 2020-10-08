||| Borrowed From Idris2 and improved with Test.Unit
module Main

import System
import System.Directory
import System.Clock

import Golden

%default total

tests : List String
tests = [ "test000"
        , "test001"
        , "test002"
        , "test003"
        , "test004"
        , "test005"
        , "test006"
        , "test007"
        ]

covering
main : IO ()
main = do  args <- getArgs

           case options args of
             Nothing =>  do {fail (usage "lightclick")}
             Just opts => do Just cwd <- currentDir | _ => fail "Unable to get cwd"
                             printLn cwd
                             results <- traverse (runTest opts cwd) (tests)
                             if any not results
                               then exitWith (ExitFailure 1)
                               else exitWith ExitSuccess

-- [ EOF ]
