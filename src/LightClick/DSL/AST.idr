module LightClick.DSL.AST

import Data.Vect

import Toolkit.Data.Location

import Language.SystemVerilog.Gates

import LightClick.Types.Direction
import LightClick.Types.Sensitivity
import LightClick.Types.WireType
import LightClick.Types.Necessity

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
       -> (nec  : Necessity)
       -> AST

  ModuleDef : {n : Nat} -> FileContext -> (kvs : Vect (S n) AST) -> AST

  Index  : FileContext -> AST -> String -> AST
  Connect : FileContext -> AST -> AST -> AST
  FanOut : {n : Nat} -> FileContext -> AST -> (ps : Vect (S (S n)) AST) -> AST
  Mux    : {n : Nat} -> FileContext -> (ps : Vect (S (S n)) AST) -> AST -> AST -> AST

  NOT  : FileContext -> AST -> AST -> AST
  GATE : {n : Nat} -> FileContext -> (ty : TyGateComb) -> (ps : Vect (S (S n)) AST) -> AST -> AST

  End : AST

mutual
  setKvsFS : String -> Vect n (Pair String AST) -> Vect n (Pair String AST)
  setKvsFS x [] = Nil
  setKvsFS x ((y, z) :: xs)
    = (y, setFileName x z) :: setKvsFS x xs

  setFSs : String -> Vect n AST -> Vect n AST
  setFSs x [] = []
  setFSs x (y :: xs) = (setFileName x y) :: setFSs x xs

  export
  setFileName : String -> AST -> AST
  setFileName fn (Ref x y)
    = Ref (setSource fn x) y

  setFileName fn (Bind x y z w)
    = Bind (setSource fn x) y (setFileName fn z) (setFileName fn w)

  setFileName fn (Seq x y)
    = Seq (setFileName fn x) (setFileName fn y)

  setFileName fn (DataLogic x)
    = DataLogic (setSource fn x)

  setFileName fn (DataArray x y k)
    = DataArray (setSource fn x) (setFileName fn y) k

  setFileName fn (DataStruct x kvs)
    = DataStruct (setSource fn x) (setKvsFS fn kvs)

  setFileName fn (DataUnion x kvs)
    = DataUnion (setSource fn x) (setKvsFS fn kvs)

  setFileName fn (Port x label dir sense wty type n)
    = (Port (setSource fn x) label dir sense wty (setFileName fn type) n)

  setFileName fn (ModuleDef x kvs)
    = ModuleDef (setSource fn x) (setFSs fn kvs)

  setFileName fn (Index x y z)
    = Index (setSource fn x) (setFileName fn y) z

  setFileName fn (Connect x y z)
    = Connect (setSource fn x) (setFileName fn y) (setFileName fn z)

  setFileName fn (FanOut x y ps)
    = FanOut (setSource fn x) (setFileName fn y) (setFSs fn ps)

  setFileName fn (Mux x ps y z)
    = Mux (setSource fn x) (setFSs fn ps) (setFileName fn y) (setFileName fn z)

  setFileName fn (NOT x y z)
    = NOT (setSource fn x) (setFileName fn y) (setFileName fn z)

  setFileName fn (GATE x ty ps y)
    = GATE (setSource fn x) ty (setFSs fn ps) (setFileName fn y)
  setFileName fn End = End

-- [ EOF ]
