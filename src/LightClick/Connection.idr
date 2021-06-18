module LightClick.Connection

import Data.Vect

import Toolkit.Decidable.Informative
import Toolkit.Data.Rig

import LightClick.Types
import LightClick.Types.Equality
import LightClick.Types.Compatibility

%default total

namespace Port

  public export
  data Compatible : (left  : Ty (PORT l))
                 -> (right : Ty (PORT r))
                          -> Type
    where
      IsSafe : (flow  : Safe                   dl dr)
            -> (sens  : Sensitivity.Compatible sl sr)
            -> (wtype : WireType.Compatible    wl wr)
            -> (dtype : Data.Compatible        tl tr)
            -> Port.Compatible (TyPort l dl sl wl tl ul)
                               (TyPort r dr sr wr tr ur)

  directionUnsafe : (Safe dir x -> Void)
                 -> Compatible (TyPort l dir sense wty type usage) (TyPort r x y z t w)
                 -> Void
  directionUnsafe contra (IsSafe flow sens wtype dtype) = contra flow

  sensitivityInCompatible : (Compatible sense y -> Void)
                         -> Compatible (TyPort l dir sense wty type usage) (TyPort r x y z t w)
                         -> Void
  sensitivityInCompatible contra (IsSafe flow sens wtype dtype) = contra sens

  wireTypesInCompatible : (Compatible wty z -> Void)
                       -> Compatible (TyPort l dir sense wty type usage) (TyPort r x y z t w)
                       -> Void
  wireTypesInCompatible contra (IsSafe flow sens wtype dtype) = contra wtype

  dataTypeInCompatible : (Compatible type t -> Void)
                    -> Compatible (TyPort l dir sense wty type usage) (TyPort r x y z t w) -> Void
  dataTypeInCompatible contra (IsSafe flow sens wtype dtype) = contra dtype

  public export
  data Error = InCompatSensitivity Sensitivity.Error
             | InCompatDirection   Direction.Safe.Error
             | InCompatWTypes      Wire.Error
             | InCompatDTypes      Data.Error



  export
  compatible : (left  : Ty (PORT l))
            -> (right : Ty (PORT r))
                     -> DecInfo Port.Error
                               (Compatible left right)
  compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) with (safe dx dy)
    compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) with (compatible sx sy)
      compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (Yes prfS) with (compatible wx wy)
        compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (Yes prfS) | (Yes prfW) with (compatible tx ty)
          compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (Yes prfS) | (Yes prfW) | (Yes prfT)
            = Yes (IsSafe prfD prfS prfW prfT)

          compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (Yes prfS) | (Yes prfW) | (No msg contra)
            = No (InCompatDTypes msg) (dataTypeInCompatible contra)
        compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (Yes prfS) | (No msg contra)
          = No (InCompatWTypes msg) (wireTypesInCompatible contra)
      compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (Yes prfD) | (No msg contra)
        = No (InCompatSensitivity msg) (sensitivityInCompatible contra)
    compatible (TyPort l dx sx wx tx ux) (TyPort r dy sy wy ty uy) | (No msg contra)
      = No (InCompatDirection msg) (directionUnsafe contra)

namespace Fanout

  namespace PortList

    public export
    data Compatible : (input : Ty (PORT s))
                   -> (fan   : DVect String (Ty . PORT) n names)
                            -> Type
      where
        Empty : PortList.Compatible i Nil
        Cons : {x : Ty (PORT s)}
            -> {rest : DVect String (Ty . PORT) n names}
            -> Port.Compatible i x
            -> PortList.Compatible i rest
            -> PortList.Compatible i (x::rest)

    headNotCompat : {xs : DVect String (Ty . PORT) n names}
                 -> (Port.Compatible i x -> Void)
                 -> PortList.Compatible i (x `DVect.(::)` xs)
                 -> Void
    headNotCompat contra (Cons prf rest) = contra prf

    restNotCompat : {xs : DVect String (Ty . PORT) n names}
                 -> (Compatible i xs -> Void)
                 -> Compatible i (x `DVect.(::)` xs)
                 -> Void
    restNotCompat contra (Cons prf rest) = contra rest

    public export
    data Error = PListError Nat (Ty (PORT s)) Port.Error

    export
    compatible : (input : Ty (PORT s))
              -> (ports : DVect String (Ty . PORT) n names)
                      -> DecInfo PortList.Error
                                 (PortList.Compatible input ports)
    compatible i Nil = Yes Empty
    compatible i (x :: xs) with (compatible i x)
      compatible i (x :: xs) | (Yes prfX) with (compatible i xs)
        compatible i (x :: xs) | (Yes prfX) | Yes prfXs = Yes (Cons prfX prfXs)

        compatible i (x :: xs) | (Yes prfX) | (No (PListError pos y err) contra)
          = No (PListError (S pos) y err) (restNotCompat contra)
      compatible i (x :: xs) | (No msg contra) = No (PListError Z x msg) (headNotCompat contra)


  public export
  data Compatible : (input : Ty (PORT s))
                 -> (fan   : DVect String (Ty . PORT) (S (S n)) names)
                 -> Type
    where
      CompatFanout : PortList.Compatible input fan
                  -> Compatible input fan

  notCompatFanout : (PortList.Compatible input (x :: (y :: fan)) -> Void)
                 -> Fanout.Compatible input (x :: (y :: fan)) -> Void
  notCompatFanout contra (CompatFanout prf) = contra prf


  export
  compatible : (input : Ty (PORT s))
            -> (fan   : DVect String (Ty . PORT) (S (S n)) names)
                     -> DecInfo PortList.Error
                                (Fanout.Compatible input fan)

  compatible input (x::y::fan) with (PortList.compatible input (x::y::fan))
    compatible input (x::y::fan) | Yes prf = Yes (CompatFanout prf)
    compatible input (x::y::fan) | No msg contra = No msg (notCompatFanout contra)

namespace Mux

  public export
  data Error = CtrlNotSafe (Ty (PORT s)) Port.Error
             | MuxNotSafe (PortList.Error)


  namespace PortList

    public export
    data Compatible : (ports : DVect String (Ty . PORT) n names)
                   -> (o     : Ty (PORT s))
                            -> Type
      where
        Empty : Compatible Nil o
        Cons : {x : Ty (PORT s)}
            -> {rest : DVect String (Ty . PORT) n names}
            -> Port.Compatible x o
            -> PortList.Compatible     rest o
            -> PortList.Compatible (x::rest) o

    headNotCompat : {xs : DVect String (Ty . PORT) n names}
                 -> (Port.Compatible x o -> Void)
                 -> PortList.Compatible (x `DVect.(::)` xs) o
                 -> Void
    headNotCompat contra (Cons prf rest) = contra prf

    restNotCompat : {xs : DVect String (Ty . PORT) n names}
                 -> (Compatible xs o -> Void)
                 -> Compatible (x `DVect.(::)` xs) o
                 -> Void
    restNotCompat contra (Cons prf rest) = contra rest


    export
    compatible : (ports : DVect String (Ty . PORT) n names)
              -> (o     : Ty (PORT s))
                        -> DecInfo PortList.Error
                                   (PortList.Compatible ports o)
    compatible Nil o = Yes Empty
    compatible (x :: xs) o with (compatible x o)
      compatible (x :: xs) o | (Yes prfX) with (compatible xs o)
        compatible (x :: xs) o | (Yes prfX) | Yes prfXs = Yes (Cons prfX prfXs)

        compatible (x :: xs) o | (Yes prfX) | (No (PListError pos y err) contra)
          = No (PListError (S pos) y err) (restNotCompat contra)
      compatible (x :: xs) o | (No msg contra) = No (PListError Z x  msg) (headNotCompat contra)

  namespace Fanin

    public export
    data Compatible : (fan   : DVect String (Ty . PORT) (S (S n)) names)
                   -> (output : Ty (PORT s))
                   -> Type
      where
        CompatFanin : PortList.Compatible fan output
                   -> Compatible fan output

    notCompatFanin : (PortList.Compatible (x :: (y :: fan)) output -> Void)
                   -> Fanin.Compatible (x :: (y :: fan)) output -> Void
    notCompatFanin contra (CompatFanin prf) = contra prf


    export
    compatible : (fan    : DVect String (Ty . PORT) (S (S n)) names)
              -> (output : Ty (PORT s))
                       -> DecInfo PortList.Error
                                  (Fanin.Compatible fan output)

    compatible (x::y::fan) output with (PortList.compatible (x::y::fan) output)
      compatible (x::y::fan) output | Yes prf = Yes (CompatFanin prf)
      compatible (x::y::fan) output | No msg contra = No msg (notCompatFanin contra)

  public export
  data Compatible : (fan    : DVect String (Ty . PORT) (S (S n)) names)
                 -> (ctrl   : Ty (PORT c))
                 -> (output : Ty (PORT o))
                           -> Type
    where
      CompatMux : (fan  : DVect String (Ty . PORT) (S (S n)) names)
               -> (ctrl : Ty (PORT c))
               -> (out  : Ty (PORT o))
               -> (safeCTRL  : Port.Compatible ctrl (Control.mkDual ctrl))
               -> (safeFanIn : Fanin.Compatible fan out)
                            -> Compatible fan ctrl out


  faninNotCompat : (Fanin.Compatible fan output -> Void)
                -> Compatible fan ctrl output -> Void
  faninNotCompat contra (CompatMux f c o prfCtrl prfFanin) = contra prfFanin

  ctrlNotCompat : {fan : DVect String (Ty . PORT) (S (S n)) names}
               -> (Port.Compatible ctrl (Control.mkDual ctrl) -> Void)
               -> Compatible fan ctrl output
               -> Void
  ctrlNotCompat contra (CompatMux f c o prfCtrl prfFanin) = contra prfCtrl

  export
  compatible : (fanin  : DVect String (Ty . PORT) (S (S n)) names)
            -> (ctrl   : Ty (PORT c))
            -> (output : Ty (PORT o))
            -> DecInfo Mux.Error
                       (Compatible fanin ctrl output)
  compatible fan ctrl output with (Fanin.compatible fan output)
    compatible fan ctrl output | (Yes prfFan) with (compatible ctrl (Control.mkDual ctrl))
      compatible fan ctrl output | (Yes prfFan) | Yes prfCtrl = Yes (CompatMux fan ctrl output prfCtrl prfFan)

      compatible fan ctrl output | (Yes prfFan) | No msg contra
        = No (CtrlNotSafe (Control.mkDual ctrl) msg) (ctrlNotCompat contra)
    compatible fan ctrl output | No msg contra
      = No (MuxNotSafe msg) (faninNotCompat contra)

-- [ EOF ]
