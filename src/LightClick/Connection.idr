||| Type-driven predicates to state valid connections.
|||
||| Module    : Connection.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| For each connection type (direct, fanout, multiplexer) we ensure
||| that the inputs and outputs are compatible.  We provide predicates
||| that describe a valid connection, and error message returning
||| decision procedures for use in the type-checker to build the
||| predicates.
|||
module LightClick.Connection

import Data.Vect

import Toolkit.Decidable.Informative
import Toolkit.Data.Rig

import LightClick.Types
import LightClick.Types.Equality
import LightClick.Types.Compatibility

%default total

||| Predicates, error definitions, and decision procedures for Ports.
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
            -> Port.Compatible (TyPort l dl sl wl nl tl)
                               (TyPort r dr sr wr nr tr)

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
  compatible (TyPort _ xd xs xw _ xt) (TyPort _ yd ys yw _ yt)
    = decInfoDo $ do prfD <- try (safe xd yd)       InCompatDirection   (\(IsSafe flow sens wtype dtype) => flow)
                     prfS <- try (compatible xs ys) InCompatSensitivity (\(IsSafe flow sens wtype dtype) => sens)
                     prfW <- try (compatible xw yw) InCompatWTypes      (\(IsSafe flow sens wtype dtype) => wtype)
                     prfT <- try (compatible xt yt) InCompatDTypes      (\(IsSafe flow sens wtype dtype) => dtype)
                     pure (IsSafe prfD prfS prfW prfT)

||| Predicates, error definitions, and decision procedures for Fanouts.
namespace Fanout

  ||| A single input is compatible with many outputs.
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

||| Predicates, error definitions, and decision procedures for
||| multiplexers.
namespace Mux

  public export
  data Error = CtrlNotSafe (Ty (PORT s)) Port.Error
             | MuxNotSafe (PortList.Error)


  ||| A mux is many outputs connecting to a single one.
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

  ||| Wrap the fanin in an explicit structure.
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
