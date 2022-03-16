module LightClick.Main

import Data.String

import System
import System.File
import System.Clock

import Toolkit.System

import LightClick.Error
import LightClick.Core
import LightClick.Types
import LightClick.Terms
import LightClick.Build
import LightClick.Synthlify
import LightClick.Values

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric
import LightClick.IR.Channel.Normalise
import LightClick.IR.Channel.MicroSV.Error
import LightClick.IR.Channel.MicroSV.Intermediate
import LightClick.IR.Channel.MicroSV

import LightClick.DSL.AST
import LightClick.DSL.Lexer
import LightClick.DSL.Parser

import Language.SystemVerilog.Micro
import Language.SystemVerilog.Micro.Pretty


processArgs : List String -> IO (Bool,String)
processArgs xs
    = do Just (t,f) <- processArgs' xs
           | Nothing => do putStrLn "Invalid args."
                           exitFailure
         pure (t,f)
  where
    processArgs' : List String -> IO $ Maybe (Bool, String)
    processArgs' (x::"--timing"::z::xs) = pure $ Just (True, z)
    processArgs' (x::y::xs) = pure $ Just (False, y)
    processArgs' _          = pure $ Nothing


lightclick : (showTiming : Bool)
          -> (fname      : String)
                        -> LightClick ()
lightclick showTiming fname
  = do ast <- fromFile fname

       log "LOG : Parsing Complete"

       term <- try showTiming
                   "LOG : Type Checking Complete"
                   termBuilder
                   ast

       value <- try showTiming
                    "LOG : Synth-lification Complete"
                    synthlify
                    term

       mir <- try showTiming
                   "LOG : Modularisation Complete"
                   modularise
                   value

       cir <- try showTiming
                   "LOG : Channelisation Complete"
                   channelise
                   mir

       cin <- try showTiming
                   "LOG : Normalisation Complete"
                   normalise
                   cir

       svi <- try showTiming
                   "LOG : Initial Pass to SystemVerilog Complete"
                   systemVerilog
                   cin

       msv <- try showTiming
                   "LOG : Final Pass to SystemVerilog Complete"
                   systemVerilog
                   svi

       putStrLn "LOG : Pretty Printing"
       printLn (prettySpec msv)

       putStrLn "LOG : BYE"

main : IO ()
main = do
  args <- getArgs
  (timing, fname) <- processArgs args
  run (\err => do printLn err; exitFailure)
      (\res => pure ())
      (lightclick timing fname)

-- [ EOF ]
