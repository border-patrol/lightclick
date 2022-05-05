||| The Core Computation Context.
|||
||| Module    : Core.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| for LightClick.
|||
module LightClick.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public LightClick.Error

%default total

public export
%inline
LightClick : Type -> Type
LightClick = TheRug LightClick.Error

namespace LightClick

  %inline
  whenErr : (msg : LightClick.Error)
                -> IO ()
  whenErr err
    = do putStrLn (unlines ["Uncaught error: ", show err])
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : LightClick a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
