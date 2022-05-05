||| Type equality.
|||
||| Module    : Equality.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.Types.Equality

import public Toolkit.Decidable.Do
import public Toolkit.Decidable.Equality.Indexed

import public Toolkit.Decidable.Informative

import Toolkit.Data.Rig

import Toolkit.Data.Vect.Extra

import Toolkit.Data.DVect.View.Shape

import LightClick.Types.Meta
import LightClick.Types.Direction
import LightClick.Types.Sensitivity
import LightClick.Types.WireType

import LightClick.Types

%default total

public export
Equals : {a,b : MTy}
      -> (x : Ty a)
      -> (y : Ty b)
      -> Type
Equals = Equals MTy Ty

-- [ Uninhabited ]

Uninhabited (Equals TyLogic (TyEnum xs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals TyLogic (TyArray ty l)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals TyLogic (TyStruct kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals TyLogic (TyUnion kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyEnum xs) (TyArray ty l)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyEnum xs) (TyStruct kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyEnum xs) (TyUnion kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyArray ty l) (TyUnion kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyArray ty l) (TyStruct kvs)) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Equals (TyStruct kvs) (TyUnion kvs')) where
  uninhabited (Same Refl Refl) impossible

Uninhabited (Vect.(::) x xs = Vect.Nil) where
  uninhabited Refl impossible

Uninhabited (Vect.Nil = Vect.(::) x xs) where
  uninhabited Refl impossible

dVectConsNil : x `DVect.(::)` xs = DVect.Nil -> Void
dVectConsNil Refl impossible

dVectNilCons : DVect.Nil = x `DVect.(::)` xs -> Void
dVectNilCons Refl impossible


-- [ Declarations ]
decEq : (x   : Ty i)
     -> (y   : Ty j)
     -> (prf : i = j)
            -> Dec (Equals MTy Ty x y)

kvpair : (x : (Pair String (Ty DATA)))
      -> (y : (Pair String (Ty DATA)))
           -> Dec (x = y)

kvpairs : (xs : Vect n (Pair String (Ty DATA)))
       -> (ys : Vect m (Pair String (Ty DATA)))
           -> Dec (xs = ys)

ports : (xs : DVect String (Ty . PORT) n ns)
     -> (ys : DVect String (Ty . PORT) m ms)
           -> Dec (xs = ys)

-- with (shape xs ys)

-- [ Definitions ]

-- ## Ports

ports {n} {ns} {m} {ms} xs ys with (shape xs ys)
  ports {n = 0} {ns = []} {m = 0} {ms = []} [] [] | Empty
    = Yes Refl

  ports {n = (S n)} {ns = (x' :: xs')} {m = 0} {ms = []} (x :: xs) [] | LH
    = No dVectConsNil
  ports {n = 0} {ns = []} {m = (S n)} {ms = (x :: xs)} [] (y :: ys) | RH
    = No (dVectNilCons)

  ports {n = (S n)} {ns = (x' :: xs')} {m = (S n)} {ms = (y' :: ys')} (x :: xs) (y :: ys) | Both
    = case decEq x' y' of
        No contra => No (\Refl => contra Refl)
        Yes Refl =>
          case decEq x y Refl of
            No contra => No (\Refl => contra (Same Refl Refl))
            Yes (Same Refl Refl) =>
              case ports xs ys of
                No contra => No (\Refl => contra Refl)
                Yes Refl => Yes Refl

-- ## KVPair

kvpair (xk, xv) (yk,yv) with (decEq xk yk)
  kvpair (xk, xv) (xk,yv) | (Yes Refl) with (decEq xv yv Refl)
    kvpair (xk, xv) (xk,xv) | (Yes Refl) | (Yes (Same Refl Refl))
      = Yes Refl
    kvpair (xk, xv) (xk,yv) | (Yes Refl) | (No contra)
      = No (\Refl => contra (Same Refl Refl))

  kvpair (xk, xv) (yk,yv) | (No contra)
    = No (\Refl => contra Refl)


-- ## KVPairs

kvpairs {n} xs {m} ys with (shape xs ys)
  kvpairs {n = 0} [] {m = 0} [] | Empty
    = Yes Refl

  kvpairs {n = (S len)} (x :: xs) {m = 0} [] | LH
    = No absurd

  kvpairs {n = 0} [] {m = (S len)} (y :: ys) | RH
    = No absurd

  kvpairs {n = (S len)} (x :: xs) {m = (S len)} (y :: ys) | Both
    = decDo $ do Refl <- kvpair x y    `otherwise` (\Refl => Refl)
                 Refl <- kvpairs xs ys `otherwise` (\Refl => Refl)
                 pure Refl

-- ## Main DecEq

decEq TyLogic y Refl with (y)
  decEq TyLogic y Refl | TyLogic
    = Yes (Same Refl Refl)

  decEq TyLogic y Refl | (TyEnum xs)
    = No absurd

  decEq TyLogic y Refl | (TyArray type length)
    = No absurd

  decEq TyLogic y Refl | (TyStruct kvs)
    = No absurd

  decEq TyLogic y Refl | (TyUnion kvs)
    = No absurd

decEq (TyEnum xs) y Refl with (y)
  decEq (TyEnum xs) y Refl | TyLogic
    = No (negEqSym absurd)

  decEq (TyEnum xs) y Refl | (TyEnum ys)
    = case decEq xs ys of
        Yes Refl => Yes (Same Refl Refl)
        No contra => No (\(Same Refl Refl) => contra Refl)

  decEq (TyEnum xs) y Refl | (TyArray type length)
    = No absurd
  decEq (TyEnum xs) y Refl | (TyStruct kvs)
    = No absurd

  decEq (TyEnum xs) y Refl | (TyUnion kvs)
    = No absurd

decEq (TyArray type length) y Refl with (y)
  decEq (TyArray type length) y Refl | TyLogic
    = No (negEqSym absurd)

  decEq (TyArray type length) y Refl | (TyEnum xs)
    = No (negEqSym absurd)

  decEq (TyArray type length) y Refl | (TyArray typeB lengthB) with (decEq type typeB Refl)
    decEq (TyArray typeB length) y Refl | (TyArray typeB lengthB) | (Yes (Same Refl Refl)) with (decEq length lengthB)
      decEq (TyArray typeB length) y Refl | (TyArray typeB length) | (Yes (Same Refl Refl)) | (Yes Refl)
        = Yes (Same Refl Refl)
      decEq (TyArray typeB length) y Refl | (TyArray typeB lengthB) | (Yes (Same Refl Refl)) | (No contra)
        = No (\(Same Refl Refl) => contra Refl)

    decEq (TyArray type length) y Refl | (TyArray typeB lengthB) | (No contra)
      = No (\(Same Refl Refl) => contra (Same Refl Refl))

  decEq (TyArray type length) y Refl | (TyStruct kvs)
    = No absurd

  decEq (TyArray type length) y Refl | (TyUnion kvs)
    = No absurd

decEq (TyStruct kvs) y Refl with (y)
  decEq (TyStruct kvs) y Refl | TyLogic
    = No (negEqSym absurd)

  decEq (TyStruct kvs) y Refl | (TyEnum xs)
    = No (negEqSym absurd)

  decEq (TyStruct kvs) y Refl | (TyArray type length)
   = No (negEqSym absurd)

  decEq (TyStruct kvs) y Refl | (TyStruct kvs') with (kvpairs kvs kvs')
    decEq (TyStruct kvs) y Refl | (TyStruct kvs) | (Yes Refl)
      = Yes (Same Refl Refl)

    decEq (TyStruct kvs) y Refl | (TyStruct kvs') | (No contra)
      = No (\(Same Refl Refl) => contra Refl)

  decEq (TyStruct kvs) y Refl | (TyUnion xs)
    = No absurd

decEq (TyUnion kvs) y Refl with (y)
  decEq (TyUnion kvs) y Refl | TyLogic
    = No (negEqSym absurd)

  decEq (TyUnion kvs) y Refl | (TyEnum xs)
    = No (negEqSym absurd)

  decEq (TyUnion kvs) y Refl | (TyArray type length)
    = No (negEqSym absurd)

  decEq (TyUnion kvs) y Refl | (TyStruct xs)
    = No (negEqSym absurd)

  decEq (TyUnion kvs) y Refl | (TyUnion kvs') with (kvpairs kvs kvs')
    decEq (TyUnion kvs) y Refl | (TyUnion kvs) | (Yes Refl)
      = Yes (Same Refl Refl)

    decEq (TyUnion kvs) y Refl | (TyUnion kvs') | (No contra)
      = No (\(Same Refl Refl) => contra Refl)

decEq TyUnit TyUnit Refl
  = Yes (Same Refl Refl)

decEq TyConn TyConn Refl
  = Yes (Same Refl Refl)

decEq TyGate TyGate Refl
  = Yes (Same Refl Refl)

decEq (TyPort xl xd xs xw xn xt) (TyPort xl yd ys yw yn yt) Refl
  = case decEq (xd,xs,xw,xn) (yd,ys,yw,yn) of
      No contra => No (\(Same Refl Refl) => contra Refl)
      Yes Refl =>
        case decEq xt yt Refl of
          No contra => No (\(Same Refl Refl) => contra (Same Refl Refl))

          Yes (Same Refl Refl) => Yes (Same Refl Refl)

decEq (TyModule x) (TyModule y) Refl with (ports x y)

  decEq (TyModule x) (TyModule x) Refl | (Yes Refl)
    = Yes (Same Refl Refl)

  decEq (TyModule x) (TyModule y) Refl | (No contra)
    = No (\(Same Refl Refl) => contra Refl)


DecEqIdx MTy Ty where
  decEq x y prf = Equality.decEq x y prf

-- [ EOF ]
