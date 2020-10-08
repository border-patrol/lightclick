module LightClick.Main

import System
import System.File
import System.Clock

import Commons.System


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
--
--timeRun : (String -> IO Either err AST) -> String -> IO (String, Either err AST)
--timeRun f a = do
--  start <- clockTime UTC
--  let res = f a
--  end <- clockTime UTC
--  let t = timeDifference start end
--  pure (show t, res)


main : IO ()
main = do
  args <- getArgs
  Just (timing, fname) <- processArgs args | Nothing =>  putStrLn "Invalid args."
  (res) <- (parseClickDesignFile fname)
  case res of
    Left (FError err) => do {putStr "File Error: "; printLn err}
    Left (PError err) => do {putStrLn $ maybe "" show (location err); putStrLn (error err)}
    Left (LError (MkLexFail l i)) => do {print l; printLn i}
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
