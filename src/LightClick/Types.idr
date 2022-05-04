module LightClick.Types

import public Data.Vect

import public Toolkit.Data.DVect
import public Toolkit.Data.Rig

import public LightClick.Types.Meta
import public LightClick.Types.Direction
import public LightClick.Types.Sensitivity
import public LightClick.Types.Necessity
import public LightClick.Types.WireType
import public LightClick.Types.EndpointKind

%default total

public export
data Ty : MTy -> Type where
  TyLogic : Ty DATA
  TyEnum : {n : Nat} -> Vect (S n) String -> Ty DATA
  TyArray : (type : Ty DATA) -> (length : Nat) -> Ty DATA
  TyStruct : {n : Nat} -> (kvs : Vect (S n) (Pair String (Ty DATA))) -> Ty DATA
  TyUnion  : {n : Nat} -> (kvs : Vect (S n) (Pair String (Ty DATA))) -> Ty DATA

  TyUnit : Ty UNIT
  TyConn : Ty CONN
  TyGate : Ty GATE

  TyPort : (label : String)
        -> (dir   : Direction)
        -> (sense : Sensitivity)
        -> (wty   : Wire)
        -> (n     : Necessity)
        -> (type  : Ty DATA)
                 -> Ty (PORT label)


  TyModule : {n : Nat}
          -> {names : Vect (S n) String}
          -> DVect String (Ty . PORT) (S n) names
          -> Ty (MODULE names)

public export
data PortHasName : (label : String) -> (Ty (PORT str)) -> Type
  where
    HasName : (label = str)
           -> PortHasName label (TyPort str d s w n t)

export
portHasName : (label : String)
           -> (port  : Ty (PORT str))
                    -> Dec (PortHasName label port)
portHasName label (TyPort str dir sense wty n type) with (decEq label str)
  portHasName label (TyPort str dir sense wty n type) | (Yes prf)
    = Yes (HasName prf)
  portHasName label (TyPort str dir sense wty n type) | (No contra)
    = No (\(HasName Refl) => contra Refl)

namespace DVect
  public export
  data HasPortNamed : (label : String)
                   -> (mod   : DVect String (Ty . PORT) n names)
                   -> (port  : Ty (PORT label))
                            -> Type
    where
      Here : {ports : DVect String (Ty . PORT) n names}
          -> PortHasName label port
          -> HasPortNamed label (port :: ports) port

      There : HasPortNamed label ports port
           -> HasPortNamed label (skipped :: ports) port

  Uninhabited (DPair (Ty (PORT l)) (HasPortNamed l Nil)) where
    uninhabited (p ** Here x) impossible
    uninhabited (p ** There x) impossible

  notPortNamed : (DPair (Ty (PORT label)) (HasPortNamed label rest) -> Void)
              -> (PortHasName label ex -> Void)
              -> DPair (Ty (PORT label)) (HasPortNamed label (ex :: rest))
              -> Void
  notPortNamed f g (MkDPair (TyPort label d s w n t) (Here (HasName Refl)))
    = g (HasName Refl)
  notPortNamed f g (MkDPair fst (There x))
    = f (MkDPair fst x)


  export
  hasPortNamed : (label : String)
              -> (mod   : DVect String (Ty . PORT) n names)
                       -> Dec (DPair (Ty (PORT label)) (HasPortNamed label mod))
  hasPortNamed label []
    = No absurd
  hasPortNamed label (ex :: rest) with (portHasName label ex)
    hasPortNamed x ((TyPort x d s w o t) :: rest) | (Yes (HasName Refl))
      = Yes (MkDPair (TyPort x d s w o t) (Here (HasName Refl)))
    hasPortNamed label (ex :: rest) | (No contra) with (hasPortNamed label rest)
      hasPortNamed label (ex :: rest) | (No contra) | (Yes (MkDPair fst snd))
        = Yes (MkDPair fst (There snd))
      hasPortNamed label (ex :: rest) | (No contra) | (No f)
        = No (notPortNamed f contra)

public export
data HasPortNamed : (label : String)
                 -> (mod   : Ty (MODULE names))
                 -> (port  : Ty (PORT label))
                          -> Type
  where
    HPN : (HasPortNamed l ms p)
       -> HasPortNamed l (TyModule ms) p

noPortFound : (DPair (Ty (PORT label)) (HasPortNamed label x) -> Void) -> DPair (Ty (PORT label)) (HasPortNamed label (TyModule x)) -> Void
noPortFound f (MkDPair fst (HPN y)) = f (MkDPair fst y)

export
hasPortNamed : (label : String)
            -> (mod   : Ty (MODULE names))
                     -> Dec (DPair (Ty (PORT label)) (HasPortNamed label mod))
hasPortNamed label (TyModule x) with (hasPortNamed label x)
  hasPortNamed label (TyModule x) | (Yes (MkDPair fst snd))
    = Yes (MkDPair fst (HPN snd))
  hasPortNamed label (TyModule x) | (No contra)
    = No (noPortFound contra)

public export
data Bindable : MTy -> Type where
  IsData : Bindable DATA
  IsModule : Bindable (MODULE names)

public export
data Seqable : MTy -> Type where
  IsGate : Seqable GATE
  IsConn : Seqable CONN

-- [ Duals ]

public export
mkDual : Ty (PORT label) -> Ty (PORT label)
mkDual (TyPort l d s w n t) with (d)
  mkDual (TyPort l d s w n t) | IN    = TyPort l OUT   s w n t
  mkDual (TyPort l d s w n t) | OUT   = TyPort l IN    s w n t
  mkDual (TyPort l d s w n t) | INOUT = TyPort l INOUT s w n t

namespace Control
  public export
  mkDual : Ty (PORT label) -> Ty (PORT label)
  mkDual (TyPort l d s w n t) with (d)
    mkDual (TyPort l d s w n t) | IN    = TyPort l OUT   s Control n t
    mkDual (TyPort l d s w n t) | OUT   = TyPort l IN    s Control n t
    mkDual (TyPort l d s w n t) | INOUT = TyPort l INOUT s Control n t

namespace EndpointKind
  export
  fromType : Ty (PORT l) -> EndpointKind
  fromType (TyPort l IN _ _ _ _)
    = DRIVER

  fromType (TyPort l OUT _ _ _ _)
    = CATCHER

  fromType (TyPort l INOUT _ _ _ _)
    = BOTH

-- [ EOF ]
