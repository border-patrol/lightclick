module LightClick.Types

import public Data.Vect

import public Toolkit.Data.DVect
import public Toolkit.Data.Rig

import public LightClick.Types.Meta
import public LightClick.Types.Direction
import public LightClick.Types.Sensitivity
import public LightClick.Types.WireType


%default total

public export
data Ty : MTy -> Type where
  TyLogic : Ty DATA
  TyArray : (type : Ty DATA) -> (length : Nat) -> Ty DATA
  TyStruct : {n : Nat} -> (kvs : Vect (S n) (Pair String (Ty DATA))) -> Ty DATA
  TyUnion  : {n : Nat} -> (kvs : Vect (S n) (Pair String (Ty DATA))) -> Ty DATA

  TyUnit : Ty UNIT
  TyConn : Ty CONN
  TyGate : Ty GATE

  TyPort : (label : String)
        -> (dir : Direction)
        -> (sense: Sensitivity)
        -> (wty : Wire)
        -> (type : Ty DATA)
        -> (usage : TyRig)
        -> Ty (PORT label)


  TyModule : {n : Nat}
          -> {names : Vect (S n) String}
          -> DVect String (Ty . PORT) (S n) names
          -> Ty (MODULE names)


-- [ Accessors and ]
public export
mkDual : Ty (PORT label) -> Ty (PORT label)
mkDual (TyPort l d s w t u) with (d)
  mkDual (TyPort l d s w t u) | IN = TyPort l OUT s w t u
  mkDual (TyPort l d s w t u) | OUT = TyPort l IN s w t u
  mkDual (TyPort l d s w t u) | INOUT = TyPort l INOUT s w t u

namespace Control
  public export
  mkDual : Ty (PORT label) -> Ty (PORT label)
  mkDual (TyPort l d s w t u) with (d)
    mkDual (TyPort l d s w t u) | IN = TyPort l OUT s Control t u
    mkDual (TyPort l d s w t u) | OUT = TyPort l IN s Control t u
    mkDual (TyPort l d s w t u) | INOUT = TyPort l INOUT s Control t u

getPortLabel : {label : String} -> Ty (PORT label) -> String
getPortLabel {label} p = label

export
getUsage : Ty (PORT s) -> TyRig
getUsage (TyPort label dir sense wty type usage) = usage

export
setUsage : Ty (PORT s) -> TyRig -> Ty (PORT s)
setUsage (TyPort label dir sense wty type _) = TyPort label dir sense wty type



-- [ EOF ]
