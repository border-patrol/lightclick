||| The Raw syntax tree definition and helper functions.
|||
||| Module    : AST.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.DSL.AST

import Data.Vect

import Toolkit.Data.Location

import Language.SystemVerilog.Gates

import LightClick.Types.Direction
import LightClick.Types.Necessity
import LightClick.Types.Sensitivity
import LightClick.Types.WireType

%default total

||| LightClicks raw syntax tree as read in by the parser.
|||
||| The shape of this tree mostly follows that of the core terms,
||| albeit with two terms that are inserted during elaboration.
|||
||| `End'` is the false end that, once encountered, connects the
||| optional ports to no-ops for linearity to hold.
|||
public export
data AST : Type where
  Ref : (fc    : FileContext)
     -> (label : String)
              -> AST

  Bind : (fc           : FileContext)
      -> (name         : String)
      -> (value, scope : AST)
               -> AST

  Seq : (this, that : AST) -> AST

  DataLogic : (fc : FileContext)
                 -> AST

  DataArray : (fc   : FileContext)
           -> (type : AST)
           -> (size : Nat)
                   -> AST

  DataEnum : {n      : Nat}
          -> (fc     : FileContext)
          -> (labels : Vect (S n) String)
                    -> AST

  DataStruct : {n      : Nat}
            -> (fc     : FileContext)
            -> (fields : Vect (S n) (String, AST))
                      -> AST

  DataUnion : {n      : Nat}
           -> (fc     : FileContext)
           -> (fields : Vect (S n) (String, AST))
                     -> AST

  Port : (fc    : FileContext)
      -> (label : String)
      -> (dir   : Direction)
      -> (sense : Sensitivity)
      -> (wty   : Wire)
      -> (n     : Necessity)
      -> (type  : AST)
               -> AST

  ModuleDef : {n   : Nat}
           -> (fc  : FileContext)
           -> (kvs : Vect (S n) AST)
                  -> AST

  Index  : (fc    : FileContext)
        -> (mname : AST)
        -> (label : String)
                 -> AST

  Connect : (fc        : FileContext)
         -> (this,that : AST)
                      -> AST
  FanOut : {n    : Nat}
        -> (fc   : FileContext)
        -> (from : AST)
        -> (tos  : Vect (S (S n)) AST)
                -> AST

  Mux : {n        : Nat}
     -> (fc       : FileContext)
     -> (froms    : Vect (S (S n)) (AST))
     -> (ctrl, to : AST)
                 -> AST

  NOT : (fc       : FileContext)
     -> (from, to : AST)
                 -> AST

  GATE : {n     : Nat}
      -> (fc    : FileContext)
      -> (ty    : TyGateComb)
      -> (froms : Vect (S (S n)) AST)
      -> (to    : AST)
               -> AST

  End : (fc : FileContext) -> AST

  NoOp : (fc   : FileContext)
      -> (this : AST)
              -> AST

  |||
  End' : (fc : FileContext) -> AST

{- [ Set filename ]

The file name is not set during parsing and generation of the spans.

Let's fix that.

-}

mutual

  {- Some helper functions to deal with totality.

  -}

  setKvsFS : String
          -> Vect n (String, AST)
          -> Vect n (String, AST)
  setKvsFS x [] = Nil
  setKvsFS x ((y, z) :: xs)
    = (y, setFileName x z) :: setKvsFS x xs

  setFSs : String
        -> Vect n (AST)
        -> Vect n (AST)
  setFSs x [] = []
  setFSs x (y :: xs) = (setFileName x y) :: setFSs x xs

  ||| Update the AST with the new file name.
  export
  setFileName : (fname : String)
             -> (ast   : AST)
                      -> AST
  setFileName fn (Ref x y)
    = Ref (setSource fn x)
          y

  setFileName fn (Bind x y z w)
    = Bind (setSource fn x)
            y
           (setFileName fn z)
           (setFileName fn w)

  setFileName fn (Seq x y)
    = Seq (setFileName fn x)
          (setFileName fn y)

  setFileName fn (DataLogic x)
    = DataLogic (setSource fn x)

  setFileName fn (DataEnum fc xs)
    = DataEnum (setSource fn fc)
               xs

  setFileName fn (DataArray x y k)
    = DataArray (setSource fn x)
                (setFileName fn y)
                k

  setFileName fn (DataStruct x kvs)
    = DataStruct (setSource fn x)
                 (setKvsFS fn kvs)

  setFileName fn (DataUnion x kvs)
    = DataUnion (setSource fn x)
                (setKvsFS fn kvs)

  setFileName fn (Port x label dir sense wty n type)
    = Port (setSource fn x)
           label
           dir
           sense
           wty
           n
           (setFileName fn type)

  setFileName fn (ModuleDef x kvs)
    = ModuleDef (setSource fn x)
                (setFSs fn kvs)

  setFileName fn (Index x y z)
    = Index (setSource fn x)
            (setFileName fn y)
            z

  setFileName fn (Connect x y z)
    = Connect (setSource fn x)
              (setFileName fn y)
              (setFileName fn z)

  setFileName fn (FanOut x y ps)
    = FanOut (setSource fn x)
             (setFileName fn y)
             (setFSs fn ps)

  setFileName fn (Mux x ps y z)
    = Mux (setSource fn x)
          (setFSs fn ps)
          (setFileName fn y)
          (setFileName fn z)

  setFileName fn (NOT x y z)
    = NOT (setSource fn x)
          (setFileName fn y)
          (setFileName fn z)

  setFileName fn (GATE x ty ps y)
    = GATE (setSource fn x)
           ty
           (setFSs fn ps)
           (setFileName fn y)

  setFileName fn (End fc)
    = End (setSource fn fc)

  setFileName fn (End' fc)
    = End' (setSource fn fc)

  setFileName fn (NoOp fc p)
    = NoOp (setSource fn fc)
           (setFileName fn p)

-- [ EOF ]
