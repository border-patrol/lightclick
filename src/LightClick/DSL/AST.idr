module LightClick.DSL.AST

import Data.Vect

import Toolkit.Data.Location

import Language.SystemVerilog.Gates

import LightClick.Types.Direction
import LightClick.Types.Sensitivity
import LightClick.Types.WireType

%default total

public export
data AST : Type where
  Ref  : FileContext -> String -> AST
  Bind : FileContext -> String -> AST -> AST -> AST
  Seq  : AST -> AST -> AST

  DataLogic  : FileContext -> AST
  DataArray  : FileContext -> AST -> Nat -> AST
  DataStruct : {n : Nat} -> FileContext -> (kvs : Vect (S n) (Pair String AST)) -> AST
  DataUnion  : {n : Nat} -> FileContext -> (kvs : Vect (S n) (Pair String AST)) -> AST

  Port  : FileContext
       -> (label : String)
       -> (dir : Direction)
       -> (sense: Sensitivity)
       -> (wty : Wire)
       -> (type : AST)
       -> AST

  ModuleDef : {n : Nat} -> FileContext -> (kvs : Vect (S n) AST) -> AST

  Index  : FileContext -> AST -> String -> AST
  Connect : FileContext -> AST -> AST -> AST
  FanOut : {n : Nat} -> FileContext -> AST -> (ps : Vect (S (S n)) AST) -> AST
  Mux    : {n : Nat} -> FileContext -> (ps : Vect (S (S n)) AST) -> AST -> AST -> AST

  NOT  : FileContext -> AST -> AST -> AST
  GATE : {n : Nat} -> FileContext -> (ty : TyGateComb) -> (ps : Vect (S (S n)) AST) -> AST -> AST

  End : AST

-- [ EOF ]
