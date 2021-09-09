module LightClick.Main

import Data.String

import System
import System.File
import System.Clock

import Toolkit.System

import LightClick.Error
import LightClick.Types
import LightClick.Terms
import LightClick.Check

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
import LightClick.DSL.Convert

import Language.SystemVerilog.Micro
import Language.SystemVerilog.Micro.Pretty

export
Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
Show a => Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]


processArgs : List String -> IO $ Maybe (Bool, String)
processArgs (x::"--timing"::z::xs) = pure $ Just (True, z)
processArgs (x::y::xs) = pure $ Just (False, y)
processArgs _          = pure $ Nothing


printLog : Bool -> Clock type -> String -> IO ()
printLog True  t m = do putStr m
                        printLn t
printLog False t m = putStrLn m


timeToTryOrDie : Show err
              => Bool
              -> String
              -> (a -> Either err type)
              -> a
              -> IO type
timeToTryOrDie timing msg f a
    = do start <- clockTime UTC
         case f a of
           Left err => do stop <- clockTime UTC
                          putStrLn "Error Happened"
                          printLn err
                          let diff = timeDifference stop start
                          printLog timing diff msg
                          exitFailure
           Right res => do stop <- clockTime UTC
                           let diff =  timeDifference stop start
                           printLog timing diff msg
                           pure res

main : IO ()
main = do
  args <- getArgs
  Just (timing, fname) <- processArgs args | Nothing => do {putStrLn "Invalid args."; exitFailure}
  (res) <- fromFile fname
  case res of
    Left err => do { printLn err; exitFailure}
    Right ast => do

      putStrLn "LOG: Parsing Complete "

      term <- timeToTryOrDie timing
                             "LOG: MetaTyping Complete "
                             runConvert
                             ast

      v <- timeToTryOrDie timing
                          "LOG: Typing Complete "
                          runCheck
                          term


--      putStrLn "LOG : Showing Values"
--      printLn v
      putStrLn "LOG : Showing ModuleIR"
      cir <- tryOrDie (ChannelCentric.runConvert (ModuleCentric.runConvert v))

--      putStrLn "LOG : Showing ChannelIR"
--      printLn cir

      putStrLn "LOG : Normalising ChannelIR"
      cirn <- tryOrDie (normalise cir)

--      putStrLn "LOG : Showing Normalised ChannelIR"
--      printLn cirn

      putStrLn "LOG : Convert to MicroSV IR"
      msvir <- tryOrDie (Intermediate.runConvert cirn)
--
      putStrLn "LOG : Convert to MicroSV"
      msv <- tryOrDie (convertSpec msvir)
--
      putStrLn "LOG : Pretty Printing"
      let prettyMSV = prettySpec msv
      printLn prettyMSV

      putStrLn "LOG : Bye"
      exitSuccess
