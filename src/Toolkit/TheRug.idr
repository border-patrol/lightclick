||| The Core Computation Context.
|||
||| Borrowed from Idris2 `Rug` is the core computation context that
||| brings the computations together.
module Toolkit.TheRug

import System
import System.File
import System.Clock
import Data.Vect

import Decidable.Equality

import Text.Parser
import Text.Lexer


import Toolkit.System
import Toolkit.Text.Parser.Run
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run

import Toolkit.Data.DList
import Toolkit.Decidable.Informative

%default total

||| Because it ties everything together.
export
record TheRug e t where
  constructor MkTheRug
  rugRun : IO (Either e t)

export
run : (whenErr : e -> IO b)
   -> (whenOK  : a -> IO b)
   -> (prog    : TheRug e a)
                   -> IO b
run whenErr whenOK (MkTheRug rugRun)
  = either whenErr
           whenOK
           !rugRun

export
%inline
fail : (msg : e)
           -> TheRug e a
fail e
  = MkTheRug (pure (Left e))

export
%inline
throw : (msg : e) -> TheRug e a
throw = fail

export
%inline
map : (a -> b)
    -> TheRug e a
    -> TheRug e b
map f (MkTheRug a)
  = MkTheRug (map (map f) a)

export
%inline
ignore : TheRug e a -> TheRug e ()
ignore
  = map (\_ => ())

export
%inline
embed : (this : IO       a)
             -> TheRug e a
embed op
  = MkTheRug (do o <- op
                 pure (Right o))

export
%inline
embed_ : (this : IO        a)
              -> TheRug e ()
embed_ this = ignore (embed this)

export
%inline
(>>=) : TheRug       e a
     -> (a -> TheRug e b)
     -> TheRug e b
(>>=) (MkTheRug act) f
  = MkTheRug (act >>=
             (\res =>
                case res of
                  Left  err => pure (Left err)
                  Right val => rugRun (f val)))

export
%inline
(>>) : TheRug e ()
    -> TheRug e a
    -> TheRug e a
(>>) ma mb = ma >>= const mb

export
%inline
pure : a -> TheRug e a
pure x = MkTheRug (pure (pure x))

export
(<*>) : TheRug e (a -> b)
     -> TheRug e  a
     -> TheRug e       b
(<*>) (MkTheRug f)
      (MkTheRug a) = MkTheRug [| f <*> a |]


export
(*>) : TheRug e a
    -> TheRug e b
    -> TheRug e b
(*>) (MkTheRug a)
     (MkTheRug b) = MkTheRug [| a *> b |]

export
(<*) : TheRug e a
    -> TheRug e b
    -> TheRug e a
(<*) (MkTheRug a)
     (MkTheRug b) = MkTheRug [| a <* b |]

export
%inline
when : (test : Bool)
    -> Lazy (TheRug e ())
    -> TheRug e ()
when False _
  = pure ()

when True f
  = f

export
%inline
tryCatch : (onErr : ea -> eb)
        -> (prog  : TheRug ea a)
                 -> TheRug eb a
tryCatch onErr prog
  = MkTheRug (run (pure . Left . onErr)
                  (pure . Right)
                  prog)

namespace Decidable
  export
  %inline
  embed : (err : b)
       -> (result : Dec      r)
                 -> TheRug b r
  embed _ (Yes prfWhy)
    = pure prfWhy

  embed err (No prfWhyNot)
    = throw err

  namespace Informative
    export
    %inline
    embed : (f : a -> b)
         -> (result : DecInfo a r)
                   -> TheRug  b r
    embed f (Yes prfWhy)
      = pure prfWhy

    embed f (No msgWhyNot prfWhyNot)
      = throw (f msgWhyNot)

namespace Traverse

  namespace List

    traverse' : (acc : List b)
             -> (f   : a -> TheRug e b)
             -> (xs  : List a)

                    -> TheRug e (List b)
    traverse' acc f []
      = pure (reverse acc)

    traverse' acc f (x :: xs)
      = traverse' (!(f x) :: acc) f xs

    export
    %inline
    traverse : (f  : a -> TheRug e b)
            -> (xs : List a)
                  -> TheRug e (List b)
    traverse = traverse' Nil

  namespace Vect
    export
    %inline
    traverse : (f  : a -> TheRug e b)
            -> (xs : Vect n a)
                  -> TheRug e (Vect n b)
    traverse f []
      = pure Nil

    traverse f (x :: xs)
      = [| f x :: traverse f xs |]

namespace IO
  export
  %inline
  putStr : (s : String)
             -> TheRug e ()
  putStr = (TheRug.embed . putStr)

  export
  %inline
  putStrLn : (s : String)
               -> TheRug e ()
  putStrLn = (TheRug.embed . putStrLn)

  export
  %inline
  print : Show a
       => (this : a)
               -> TheRug e ()
  print = (TheRug.embed . print)

  export
  %inline
  printLn : Show a
         => (this : a)
                 -> TheRug e ()
  printLn = (TheRug.embed . printLn)

  export
  covering -- not my fault
  readFile : (onErr : String -> FileError -> e)
          -> (fname : String)
                   -> TheRug e String
  readFile onErr fname
    = do Right content <- (TheRug.embed (readFile fname))
           | Left err => throw (onErr fname err)
         pure content

namespace Parsing
  export
  covering -- not my fault
  parseFile : {e     : _}
           -> (onErr : ParseError a -> err)
           -> (lexer : Lexer a)
           -> (rule  : Grammar () a e ty)
           -> (fname : String)
                    -> TheRug err ty
  parseFile onErr lexer rule fname
      = do Right res <- TheRug.embed (parseFile lexer rule fname)
                 | Left err => throw (onErr err)
           pure res


namespace Cheap
  export
  %inline
  log : (msg      : String)
                 -> TheRug e ()
  log = putStrLn


  namespace Timed
    export
    %inline
    log : (showTime : Bool)
       -> (time     : Lazy (Clock type))
       -> (msg      : String)
                   -> TheRug e ()
    log showTime t m
      = if showTime
        then do print t
                putStrLn m
        else putStrLn m

    export
    %inline
    try : Show e
       => (showTime : Bool)
       -> (msg      : String)
       -> (f        : a -> TheRug e b)
       -> (val      : a)
                   -> TheRug e b
    try showTime msg f val
      = do start <- (embed $ clockTime UTC)
           res   <- embed  (run (\err => do stop <- clockTime UTC
                                            putStrLn "Error Happened"
                                            printLn err
                                            let d = timeDifference stop start
                                            if showTime
                                              then do print d
                                                      putStrLn msg
                                                      exitFailure
                                              else do putStrLn msg
                                                      exitFailure)
                                (\res => do stop <- clockTime UTC
                                            let d = timeDifference stop start
                                            if showTime
                                              then do print d
                                                      putStrLn msg
                                                      pure res
                                              else do putStrLn msg
                                                      pure res)

                                (f val))
           pure res



-- [ EOF ]
