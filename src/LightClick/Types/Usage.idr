module LightClick.Types.Usage

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Error

import LightClick.Types
import LightClick.Types.Views
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

  state pred dec ((TyPort l d s w t n u) :: ports) with (dec l (TyPort l d s w t n u))
    state pred dec ((TyPort l d s w t n u) :: ports) | (Yes prf) with (state pred dec ports)
      state pred dec ((TyPort l d s w t n u) :: ports) | (Yes prf) | (MkState xs pos ns neg division)
        = MkState (l::xs) ((TyPort l d s w t n u)::pos) ns neg (Pos prf division)

    state pred dec ((TyPort l d s w t n u) :: ports) | (No contra) with (state pred dec ports)
      state pred dec ((TyPort l d s w t n u) :: ports) | (No contra) | (MkState xs pos ns neg division)
        = MkState xs pos (l::ns) ((TyPort l d s w t n u)::neg) (Neg contra division)

namespace Free

  namespace Port
    ||| Free ports that are bad if unused.
    |||
    ||| We restrict this to REQ unused ports
    |||
    ||| Optional ports don't matter...
    public export
    data Free : (l : String)
             -> (p : Ty (PORT l))
                  -> Type
      where
        IsReq : (l : String)
             -> (u : TyRig)
             -> (c : Not (u = None))
                  -> Free l (TyPort l d s e t REQ u)



    used : Free l (TyPort l d s w t REQ None) -> Void
    used (IsReq l None contra)
      = contra Refl

    isOptional : Free label (TyPort label d s w t OPT u) -> Void
    isOptional (IsReq l x c) impossible

    export
    free : (label : String)
        -> (type  : Ty (PORT label))
                 -> Dec (Free label type)
    free label type with (necessity type)
      free label (TyPort label d s w t REQ None) | REQ
        = No used

      free label (TyPort label d s w t REQ One) | REQ
        = Yes (IsReq label One (negEqSym noneNotOne))

      free label (TyPort label d s w t REQ Tonne) | REQ
        = Yes (IsReq label Tonne (negEqSym noneNotTonne))

      free label (TyPort label d s w t OPT u) | OPT
        = No isOptional

  namespace Types

    export
    free : (type : Ty m) -> List String
    free TyLogic = Nil
    free (TyArray type length) = Nil
    free (TyStruct kvs) = Nil
    free (TyUnion kvs) = Nil
    free TyUnit = Nil
    free TyConn = Nil
    free TyGate = Nil
    free (TyPort label dir sense wty type nec usage) with (free label (TyPort label dir sense wty type nec usage))
      free (TyPort label dir sense wty type REQ usage) | Yes (IsReq label usage contra)
        = [label]
      free (TyPort label dir sense wty type nec usage) | No contra
        = Nil
    free (TyModule ports) with (state Port.Free Port.free ports)
      free (TyModule ports) | (MkState ps pos ns neg division) = toList ps

-- --------------------------------------------------------------------- [ EOF ]
