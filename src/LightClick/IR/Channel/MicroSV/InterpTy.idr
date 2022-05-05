||| Ways & means to interprete between IR Types & SystemVerilog
||| types.
|||
||| Module    : InterpTy.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.IR.Channel.MicroSV.InterpTy

import LightClick.IR.ModuleCentric
import LightClick.Types.Direction

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Direction

%default total

export
interpDir : Types.Direction.Direction
         -> SystemVerilog.Direction.Direction
interpDir IN = IN
interpDir OUT = OUT
interpDir INOUT = INOUT

||| Correct interpretations.
public export
data InterpTy : TyIR -> Ty -> Type where
  PP : (x : String) -> InterpTy PORT   (PORT x)
  UU : InterpTy UNIT   UNIT
  MM : (xs : List String) -> InterpTy MODULE (MODULE xs)
  CM : (xs : List String) -> InterpTy CONN   (MINST xs)
  DD : InterpTy DATA   DATA
  CC : InterpTy CHAN   CHAN
  GG : InterpTy GATE   GINST

public export
getTy : {ty : Ty} -> InterpTy type ty -> Ty
getTy {ty} _ = ty

-- [ Ports ]

Uninhabited (InterpTy PORT (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT (MINST xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy PORT GINST) where
  uninhabited (PP _) impossible

-- [ Unit ]

Uninhabited (InterpTy UNIT (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT (MINST x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy UNIT GINST) where
  uninhabited (PP _) impossible

-- [ Module ]

Uninhabited (InterpTy MODULE UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE (MINST x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy MODULE GINST) where
  uninhabited (PP _) impossible

-- [ Data ]

Uninhabited (InterpTy DATA (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA (MINST x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy DATA GINST) where
  uninhabited (PP _) impossible

-- [ Conns ]

Uninhabited (InterpTy CONN (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CONN GINST) where
  uninhabited (PP _) impossible

-- [ Channel ]

Uninhabited (InterpTy CHAN (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN (MINST x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN GATE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy CHAN GINST) where
  uninhabited (PP _) impossible


-- [ Gates ]

Uninhabited (InterpTy GATE (MODULE xs)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE UNIT) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE (MINST x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE (PORT x)) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE DATA) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE TYPE) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE CHAN) where
  uninhabited (PP _) impossible

Uninhabited (InterpTy GATE GATE) where
  uninhabited (PP _) impossible

-- [ Do the Interpretation ]

||| Is this a valid interpretation
export
interpTy : (ty   : TyIR)
        -> (type : Ty)
                -> Dec (InterpTy ty type)

interpTy PORT (MODULE xs) = No absurd
interpTy PORT DATA        = No absurd
interpTy PORT CHAN        = No absurd
interpTy PORT (PORT x)    = Yes (PP x)
interpTy PORT (MINST xs)  = No absurd
interpTy PORT UNIT        = No absurd
interpTy PORT TYPE        = No absurd
interpTy PORT GATE        = No absurd
interpTy PORT GINST       = No absurd

interpTy UNIT (MODULE xs) = No absurd
interpTy UNIT DATA        = No absurd
interpTy UNIT CHAN        = No absurd
interpTy UNIT (PORT x)    = No absurd
interpTy UNIT (MINST xs)  = No absurd
interpTy UNIT UNIT        = Yes UU
interpTy UNIT TYPE        = No absurd
interpTy UNIT GATE        = No absurd
interpTy UNIT GINST       = No absurd

interpTy MODULE (MODULE xs) = Yes (MM xs)
interpTy MODULE DATA        = No absurd
interpTy MODULE CHAN        = No absurd
interpTy MODULE (PORT x)    = No absurd
interpTy MODULE (MINST xs)  = No absurd
interpTy MODULE UNIT        = No absurd
interpTy MODULE TYPE        = No absurd
interpTy MODULE GATE        = No absurd
interpTy MODULE GINST       = No absurd

interpTy CONN (MODULE xs) = No absurd
interpTy CONN DATA        = No absurd
interpTy CONN CHAN        = No absurd
interpTy CONN (PORT x)    = No absurd
interpTy CONN (MINST xs)  = Yes (CM xs)
interpTy CONN UNIT        = No absurd
interpTy CONN TYPE        = No absurd
interpTy CONN GATE        = No absurd
interpTy CONN GINST       = No absurd

interpTy DATA (MODULE xs) = No absurd
interpTy DATA DATA        = Yes DD
interpTy DATA CHAN        = No absurd
interpTy DATA (PORT x)    = No absurd
interpTy DATA (MINST xs)  = No absurd
interpTy DATA UNIT        = No absurd
interpTy DATA TYPE        = No absurd
interpTy DATA GATE        = No absurd
interpTy DATA GINST       = No absurd

interpTy CHAN (MODULE xs) = No absurd
interpTy CHAN DATA        = No absurd
interpTy CHAN CHAN        = Yes CC
interpTy CHAN (PORT x)    = No absurd
interpTy CHAN (MINST xs)  = No absurd
interpTy CHAN UNIT        = No absurd
interpTy CHAN TYPE        = No absurd
interpTy CHAN GATE        = No absurd
interpTy CHAN GINST       = No absurd

interpTy GATE (MODULE xs) = No absurd
interpTy GATE DATA        = No absurd
interpTy GATE CHAN        = No absurd
interpTy GATE (PORT x)    = No absurd
interpTy GATE (MINST xs)  = No absurd
interpTy GATE UNIT        = No absurd
interpTy GATE TYPE        = No absurd
interpTy GATE GATE        = No absurd
interpTy GATE GINST       = Yes GG

||| Predicates to define valid binders in our IR's types.
namespace TyIR

  public export
  data IsGlobal : TyIR -> Type where
    IsDeclM : IsGlobal MODULE
    IsDeclD : IsGlobal DATA

  public export
  data IsLocal : TyIR -> Type where
    IsInstM : IsLocal CONN
    IsInstC : IsLocal CHAN
    IsInstG : IsLocal GATE

  public export
  data Bindable : TyIR -> Type where
    IsDecl : IsGlobal type -> Bindable type
    IsLet  : IsLocal type  -> Bindable type
    Unbindable : TyIR.Bindable type

  export
  isBindable : (type : TyIR) -> Bindable type
  isBindable PORT = Unbindable
  isBindable UNIT = Unbindable
  isBindable MODULE = IsDecl IsDeclM
  isBindable CONN = IsLet IsInstM
  isBindable DATA = IsDecl IsDeclD
  isBindable CHAN = IsLet IsInstC
  isBindable GATE = IsLet IsInstG

-- [ EOF ]
