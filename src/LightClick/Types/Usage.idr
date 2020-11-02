module LightClick.Types.Usage

import Data.List
import Data.Vect
import Data.DList
import Data.DVect

import LightClick.Error

import LightClick.Types
import LightClick.Types.Equality

%default total

public export
PortList : (p     : Nat)
        -> (names : Vect p String)
                 -> Type
PortList = DVect String (Ty . PORT)

namespace PortList

  public export
  data Division : (0 pred : (label : String) -> Ty (PORT label) -> Type)

               -> {ps    : Vect p String}
               -> {ns    : Vect n String}
               -> {names : Vect o String}

               -> (pos  : PortList p ps)
               -> (neg  : PortList n ns)
               -> (orig : PortList o names)
                       -> Type
    where
      Empty : Division pred Nil Nil Nil

      Pos : {0 pred : (label : String) -> Ty (PORT label) -> Type}
         -> {pos  : PortList p ps}
         -> {neg  : PortList n ns}
         -> {orig : PortList o os}

         -> {label : String}
         -> {port : Ty (PORT label)}

         -> (prf  : pred label port)
         -> (rest : Division pred        pos  neg        orig)
                 -> Division pred (port::pos) neg (port::orig)

      Neg : {0 pred : (label : String) -> Ty (PORT label) -> Type}
         -> {pos  : PortList p ps}
         -> {neg  : PortList n ns}
         -> {orig : PortList o os}

         -> {label : String}
         -> {port : Ty (PORT label)}

         -> (prf  : Not (pred label port))

         -> (rest : Division pred pos        neg         orig)
                 -> Division pred pos (port::neg) (port::orig)

  public export
  data State : (pred  : (label : String) -> (port : Ty (PORT label)) -> Type)
            -> (ports : PortList p names)
                     -> Type
    where

      MkState : {0 pred : (label : String) -> Ty (PORT label) -> Type}

             -> {os       : Vect     o String}
             -> {orig     : PortList o os}

             -> (ps       : Vect     p String)
             -> (pos      : PortList p ps)

             -> (ns       : Vect     n String)
             -> (neg      : PortList n ns)

             -> (division : Division pred pos neg orig)

                         -> State pred orig

  export
  state : (0 pred  : (label : String) -> (port : Ty (PORT label)) -> Type)

       -> (dec   : (label : String) -> (port : Ty (PORT label)) -> Dec (pred label port))
       -> (ports : PortList p ps)
                -> State pred ports
  state pred _ [] = MkState Nil Nil Nil Nil Empty

  state pred dec ((TyPort l d s w t u) :: ports) with (dec l (TyPort l d s w t u))
    state pred dec ((TyPort l d s w t u) :: ports) | (Yes prf) with (state pred dec ports)
      state pred dec ((TyPort l d s w t u) :: ports) | (Yes prf) | (MkState xs pos ns neg division)
        = MkState (l::xs) ((TyPort l d s w t u)::pos) ns neg (Pos prf division)

    state pred dec ((TyPort l d s w t u) :: ports) | (No contra) with (state pred dec ports)
      state pred dec ((TyPort l d s w t u) :: ports) | (No contra) | (MkState xs pos ns neg division)
        = MkState xs pos (l::ns) ((TyPort l d s w t u)::neg) (Neg contra division)

namespace Free

  namespace Port
    public export
    data Free : (l : String) -> (port : Ty (PORT l)) -> Type where
      FreePort : (label : String)
              -> (use : TyRig)
              -> (contra : Not (use = None))
              -> Free (label) (TyPort label dir sense ety type use)

    used : Free l (TyPort l d s w t None) -> Void
    used (FreePort l None contra) = contra Refl

    export
    free : (label : String)
        -> (type  : Ty (PORT label))
                 -> Dec (Free label type)
    free l (TyPort l d s w t None) = No used
    free l (TyPort l d s w t One) = Yes (FreePort l One (negEqSym noneNotOne))
    free l (TyPort l d s w t Tonne) = Yes (FreePort l Tonne (negEqSym noneNotTonne))

  namespace Types

    export
    free : (type : Ty m) -> List String
    free TyLogic = Nil
    free (TyArray type length) = Nil
    free (TyStruct kvs) = Nil
    free (TyUnion kvs) = Nil
    free TyUnit = Nil
    free TyConn = Nil
    free (TyPort label dir sense wty type usage) with (free label (TyPort label dir sense wty type usage))
      free (TyPort label dir sense wty type usage) | Yes (FreePort label usage contra)
        = [label]
      free (TyPort label dir sense wty type usage) | No contra
        = Nil
    free (TyModule ports) with (state Port.Free Port.free ports)
      free (TyModule ports) | (MkState ps pos ns neg division) = toList ps

-- --------------------------------------------------------------------- [ EOF ]
