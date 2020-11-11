module LightClick.Types.Equality

import public Toolkit.Decidable.Equality.Indexed

import public Toolkit.Decidable.Informative

import Toolkit.Data.Rig

import Toolkit.Data.Vect.Extra

import LightClick.Error

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

-- [ No's for Logic vs X]
namespace Logic
  export
  logicNotStruct : (Equals TyLogic (TyStruct xs)) -> Void
  logicNotStruct (Same _ _) impossible

  export
  logicNotUnion : (Equals TyLogic (TyUnion xs)) -> Void
  logicNotUnion (Same _ _ ) impossible

  export
  logicNotArray : (Equals TyLogic (TyArray x k)) -> Void
  logicNotArray (Same _ _) impossible

-- [ No's for Array vs X]
namespace Array
  export
  arrayNotStruct : (Equals (TyArray x k) (TyStruct xs)) -> Void
  arrayNotStruct (Same _ _) impossible

  export
  arrayNotUnion  : (Equals (TyArray x k) (TyUnion xs)) -> Void
  arrayNotUnion (Same _ _) impossible

  export
  arrayDiffIndicies : {k,j : Nat}
                   -> (contra : (k = j) -> Void)
                   -> (Equals (TyArray x k) (TyArray y j))
                   -> Void
  arrayDiffIndicies contra (Same Refl Refl) {k = j} {j = j} = contra Refl

  export
  arrayDiffTypes : (contra : (x `Equals` y) -> Void)
                -> (Equals (TyArray x k) (TyArray y j))
                -> Void
  arrayDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

-- [ No's for 'Bodies' vs X]
namespace Body

  namespace Length
    export
    structNotUnion : (TyStruct xs `Equals` TyUnion ys) -> Void
    structNotUnion (Same _ _) impossible

    export
    structDifferBody : {xs : Vect (S n) (Pair String (Ty DATA))}
                    -> {ys : Vect (S m) (Pair String (Ty DATA))}
                    -> (contra : (xs = ys) -> Void)
                    -> (TyStruct xs `Equals` TyStruct ys)
                    -> Void
    structDifferBody contra (Same Refl Refl) = contra Refl

    export
    unionDifferBody : {xs : Vect (S n) (Pair String (Ty DATA))}
                   -> {ys : Vect (S m) (Pair String (Ty DATA))}
                   -> (contra : (xs = ys) -> Void)
                   -> (TyUnion xs `Equals` TyUnion ys)
                   -> Void
    unionDifferBody contra (Same Refl Refl) = contra Refl

    export
    modDifferBody : {xs : DVect String (Ty . PORT) (S n) ns}
                 -> {ys : DVect String (Ty . PORT) (S m) ms}
                 -> (contra : (xs = ys) -> Void)
                 -> (TyModule xs `Equals` TyModule ys)
                 -> Void
    modDifferBody contra (Same Refl Refl) = contra Refl


-- [ No's for Ports]
namespace Ports
  export
  portDifferUsage : (contra : (ux = uy) -> Void)
                 -> (TyPort lx dy sy wx ty ux `Equals` TyPort lx dy sy wx ty uy)
                 -> Void
  portDifferUsage contra (Same Refl Refl) = contra Refl

  export
  portDifferType :  (contra : (tx `Equals` ty) -> Void)
                -> (TyPort lx dy sy wx tx ux `Equals` TyPort lx dy sy wy ty uy)
                -> Void
  portDifferType contra (Same Refl Refl) = contra (Same Refl Refl)


  export
  portDifferWire : (contra : (wx = wy) -> Void)
                -> (TyPort lx dy sy wx tx ux `Equals` TyPort lx dy sy wy ty uy)
                -> Void
  portDifferWire contra (Same Refl Refl) = contra Refl

  export
  portDifferSens : (contra : (sx = sy) -> Void)
                -> (TyPort lx dy sx wx tx ux `Equals` TyPort lx dy sy wy ty uy)
                -> Void
  portDifferSens contra (Same Refl Refl) = contra Refl

  export
  portsDifferDir : (contra : (dx = dy) -> Void)
                -> (TyPort a dx sx wx tx ux `Equals` TyPort a dy sy wy ty uy)
                -> Void
  portsDifferDir contra (Same Refl Refl) = contra Refl

  export
  portsDifferLabel : (contra : (lx = ly) -> Void)
                  -> (TyPort lx dx sx wx tx ux `Equals` TyPort ly dy sy wy ty uy)
                  -> Void
  portsDifferLabel contra (Same Refl Refl) = contra Refl

-- [ No's for Body ]
namespace Body
  namespace Length
    export
    dataBodyLengthsDiffer : {xs : Vect n (Pair String (Ty DATA))}
                         -> {ys : Vect m (Pair String (Ty DATA))}
                         -> (contra : (n = m) -> Void)
                         -> (xs = ys)
                         -> Void
    dataBodyLengthsDiffer contra Refl = contra Refl

    export
    dataBodyLengthsDiffer' : {xs : Vect (S n) (Pair String (Ty DATA))}
                          -> {ys : Vect (S m) (Pair String (Ty DATA))}
                          -> (contra : (xs = ys) -> Void)
                          -> (xs = ys)
                          -> Void
    dataBodyLengthsDiffer' contra Refl = contra Refl

  namespace Values

    namespace Names
      export
      modBodyDiffer : {n : Nat}
                   -> {names : Vect (S n) String}
                   -> {xs : DVect String (Ty . PORT) (S n) names}
                   -> {ys : DVect String (Ty . PORT) (S n) names}
                   -> (contra : (xs = ys) -> Void)
                   -> (TyModule xs `Equals` TyModule ys)
                   -> Void
      modBodyDiffer contra (Same Refl Refl) = contra Refl


    namespace Rest
      export
      restDataBodyDiffer : {xs : Vect n (Pair String (Ty DATA))}
                        -> {ys : Vect n (Pair String (Ty DATA))}
                        -> (contra : (xs = ys) -> Void)
                        -> (((ky, vy) :: xs) = ((ky, vy) :: ys))
                        -> Void
      restDataBodyDiffer contra Refl = contra Refl

      export
      dataBodyDiffer : {xs : Vect n (Pair String (Ty DATA))}
                    -> {ys : Vect n (Pair String (Ty DATA))}
                    -> (contra : (xs = ys) -> Void)
                    -> (xs = ys)
                    -> Void
      dataBodyDiffer contra Refl = contra Refl



      vRestDiffer : {xs : Vect n (Pair String (Ty DATA))}
                 -> {ys : Vect m (Pair String (Ty DATA))}
                 -> (contra : (xs = ys) -> Void)
                 -> (((ky, vy) :: xs) = ((ky, vy) :: ys))
                 -> Void
      vRestDiffer contra Refl = contra Refl

      export
      dVectElemDiffer : {n : Nat}
                     -> {ns : Vect n String}
                     -> {xrest : DVect String (Ty . PORT) n ns}
                     -> {yrest : DVect String (Ty . PORT) n ns}
                     -> {x : String}
                     -> {ex : Ty (PORT x)}
                     -> {ey : Ty (PORT x)}
                     -> (contra : (ex `Equals` ey) -> Void)
                     -> ((ex :: xrest) = (ey :: yrest))
                     -> Void
      dVectElemDiffer contra Refl = contra (Same Refl Refl)

      export
      dVectBodyDiffer : {xrest : DVect String (Ty . PORT) n ns}
                     -> {yrest : DVect String (Ty . PORT) n ns}
                     -> (contra : (xrest = yrest) -> Void)
                     -> ((ey :: xrest) = (ey :: yrest))
                     -> Void
      dVectBodyDiffer contra Refl = contra Refl

    namespace Head
      export
      elemDataBodyDiffer : {xs : Vect n (Pair String (Ty DATA))}
                        -> {ys : Vect n (Pair String (Ty DATA))}
                        -> {vx, vy : Ty DATA}
                        -> (contra : (vx `Equals` vy) -> Void)
                        -> (((ky, vx) :: xs) = ((ky, vy) :: ys))
                        -> Void
      elemDataBodyDiffer contra Refl = contra (Same Refl Refl)

      export
      elemDataKeyDiffer : {xs : Vect n (Pair String (Ty DATA))}
                       -> {ys : Vect n (Pair String (Ty DATA))}
                       -> {vx, vy : Ty DATA}
                       -> (contra : (kx = ky) -> Void)
                       -> (((kx, vx) :: xs) = ((ky, vy) :: ys))
                       -> Void
      elemDataKeyDiffer contra Refl = contra Refl


export
decEq : (x : Ty i)
     -> (y : Ty j)
     -> (prf : i = j)
     -> Dec (Equals MTy Ty x y)

namespace Fields

  differentLengthLeft : {y : String}
                     -> {z : Ty DATA}
                     -> (y, z) `Vect.(::)` (x `Vect.(::)` xs) = (y, z) `Vect.(::)` Nil -> Void
  differentLengthLeft _ impossible

  differentLengthRight : {y : String}
                      -> {z : Ty DATA}
                      -> (y, z) `Vect.(::)` Nil = (y, z) `Vect.(::)` (x `Vect.(::)` xs) -> Void
  differentLengthRight _ impossible

  headTypeDiff : {xs : Vect m (Pair String (Ty DATA))}
              -> {ys : Vect n (Pair String (Ty DATA))}
              -> {z,w : Ty DATA}
              -> (Equals MTy Ty z w -> Void)
              -> (y, z) `Vect.(::)` xs = (y, w) `Vect.(::)` ys
              -> Void
  headTypeDiff contra Refl = contra (Same Refl Refl)

  headLabelDiff : {xs : Vect m (Pair String (Ty DATA))}
               -> {ys : Vect n (Pair String (Ty DATA))}
               -> (x = y -> Void)
               -> {z,w : Ty DATA}
               -> (x, z) `Vect.(::)` xs = (y, w) `Vect.(::)` ys
               -> Void
  headLabelDiff contra Refl = contra Refl

  fieldsAreNotEqual : {xs : Vect m (Pair String (Ty DATA))}
                   -> {ys : Vect n (Pair String (Ty DATA))}
                   -> (x `Vect.(::)` xs = y' `Vect.(::)` ys -> Void)
                   -> (y, z) `Vect.(::)` (x `Vect.(::)` xs) = (y, z) `Vect.(::)` (y' `Vect.(::)` ys)
                   -> Void
  fieldsAreNotEqual contra Refl = contra Refl

  export
  decEq : (xs : Vect (S n) (Pair String (Ty DATA)))
       -> (ys : Vect (S m) (Pair String (Ty DATA)))
             -> Dec (xs = ys)
  decEq {n} xs {m} ys  with (shape xs ys)
    decEq {n = n} ((x, z) :: xs) {m = m} ((y, w) :: ys) | Both with (decEq x y)
      decEq {n = n} ((y, z) :: xs) {m = m} ((y, w) :: ys) | Both | (Yes Refl) with (Equality.decEq z w Refl)
        decEq {n = n} ((y, z) :: xs) {m = m} ((y, z) :: ys) | Both | (Yes Refl) | (Yes (Same Refl Refl)) with (shape xs ys)
          decEq {n = 0} ((y, z) :: []) {m = 0} ((y, z) :: []) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | Empty = Yes Refl

          decEq {n = (S len)} ((y, z) :: (x :: xs)) {m = 0} ((y, z) :: []) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | LH = No differentLengthLeft
          decEq {n = 0} ((y, z) :: []) {m = (S len)} ((y, z) :: (y' :: ys)) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | RH = No differentLengthRight

          decEq {n = (S len)} ((y, z) :: (x :: xs)) {m = (S len)} ((y, z) :: (y' :: ys)) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | Both with (Fields.decEq (x::xs) (y'::ys))
            decEq {n = (S len)} ((y, z) :: (x :: xs)) {m = (S len)} ((y, z) :: (x :: xs)) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | Both | (Yes Refl) = Yes Refl
            decEq {n = (S len)} ((y, z) :: (x :: xs)) {m = (S len)} ((y, z) :: (y' :: ys)) | Both | (Yes Refl) | (Yes (Same Refl Refl)) | Both | (No contra) = No (fieldsAreNotEqual contra)

        decEq {n = n} ((y, z) :: xs) {m = m} ((y, w) :: ys) | Both | (Yes Refl) | (No contra) = No (headTypeDiff contra)
      decEq {n = n} ((x, z) :: xs) {m = m} ((y, w) :: ys) | Both | (No contra) = No (headLabelDiff contra)

namespace Port

  export
  decEq : (x : Ty (PORT a))
       -> (y : Ty (PORT b))
       -> Dec (Equals x y)
  decEq (TyPort a dx sx wx tx ux) (TyPort b dy sy wy ty uy) with (decEq a b)
    decEq (TyPort a dx sx wx tx ux) (TyPort a dy sy wy ty uy) | (Yes Refl) with (decEq dx dy)
      decEq (TyPort a dx sx wx tx ux) (TyPort a dx sy wy ty uy) | (Yes Refl) | (Yes Refl) with (decEq sx sy)
        decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wy ty uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) with (decEq wx wy)
          decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wx ty uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl) with (decEq tx ty Refl)
            decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wx tx uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes (Same Refl Refl)) with (decEq ux uy)
              decEq (TyPort a dx sx wx tx uy) (TyPort a dx sx wx tx uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes (Same Refl Refl)) | (Yes Refl) = Yes (Same Refl Refl)
              decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wx tx uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes (Same Refl Refl)) | (No contra) = No (portDifferUsage contra)
            decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wx ty uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (No contra) = No (portDifferType contra)

          decEq (TyPort a dx sx wx tx ux) (TyPort a dx sx wy ty uy) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (No contra) = No (portDifferWire contra)
        decEq (TyPort a dx sx wx tx ux) (TyPort a dx sy wy ty uy) | (Yes Refl) | (Yes Refl) | (No contra) = No (portDifferSens contra)
      decEq (TyPort a dx sx wx tx ux) (TyPort a dy sy wy ty uy) | (Yes Refl) | (No contra) = No (portsDifferDir contra)
    decEq (TyPort a dx sx wx tx ux) (TyPort b dy sy wy ty uy) | (No contra) = No (portsDifferLabel contra)


namespace Ports

  export
  decEq : {n :Nat}
       -> {ns : _}
       -> (xs : DVect String (Ty . PORT) n ns)
       -> (ys : DVect String (Ty . PORT) n ns)
             -> Dec (xs = ys)
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (Port.decEq x y)
    decEq (x :: xs) (x :: ys) | (Yes (Same Refl Refl)) with (Ports.decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes (Same Refl Refl)) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (y :: ys) | (Yes (Same Refl Refl)) | (No contra) = No (dVectBodyDiffer contra)
    decEq (x :: xs) (y :: ys) | (No contra) = No (dVectElemDiffer contra)

-- [ Body ]

-- [ Logic Types]
decEq TyLogic TyLogic Refl = Yes (Same Refl Refl)
decEq TyLogic (TyArray x k) Refl = No logicNotArray
decEq TyLogic (TyStruct xs) Refl = No logicNotStruct
decEq TyLogic (TyUnion xs) Refl = No logicNotUnion

-- [ Array Types ]
decEq (TyArray x k) TyLogic Refl = No (negEqSym logicNotArray)

decEq (TyArray x i) (TyArray y j) Refl with (decEq i j)
  decEq (TyArray x i) (TyArray y i) Refl | (Yes Refl) with (decEq x y Refl)
    decEq (TyArray x i) (TyArray x i) Refl | (Yes Refl) | (Yes (Same Refl Refl))
      = Yes (Same Refl Refl)
    decEq (TyArray x i) (TyArray y i) Refl | (Yes Refl) | (No contra)
      = No (arrayDiffTypes contra)
  decEq (TyArray x i) (TyArray y j) Refl | (No contra)
    = No (arrayDiffIndicies contra)

decEq (TyArray x k) (TyStruct xs) Refl = No arrayNotStruct
decEq (TyArray x k) (TyUnion xs) Refl = No arrayNotUnion

-- [ Structs ]
decEq (TyStruct xs) TyLogic Refl = No (negEqSym logicNotStruct)
decEq (TyStruct xs) (TyArray type length) Refl = No (negEqSym arrayNotStruct)

decEq (TyStruct xs) (TyStruct ys) Refl with (Fields.decEq xs ys)
  decEq (TyStruct xs) (TyStruct xs) Refl | (Yes Refl)  = Yes (Same Refl Refl)
  decEq (TyStruct xs) (TyStruct ys) Refl | (No contra) = No (structDifferBody contra)

decEq (TyStruct xs) (TyUnion kvs) Refl = No structNotUnion

-- [ Unions ]
decEq (TyUnion xs) TyLogic Refl = No (negEqSym logicNotUnion)
decEq (TyUnion xs) (TyArray type length) Refl = No (negEqSym arrayNotUnion)
decEq (TyUnion xs) (TyStruct kvs) Refl = No (negEqSym structNotUnion)

decEq (TyUnion xs) (TyUnion ys) Refl with (Fields.decEq xs ys)
  decEq (TyUnion xs) (TyUnion xs) Refl | (Yes Refl)   = Yes (Same Refl Refl)
  decEq (TyUnion xs) (TyUnion ys) Refl | (No  contra) = No (unionDifferBody contra)

-- [ Unit ]
decEq TyUnit TyUnit Refl = Yes (Same Refl Refl)

-- [ Gates ]
decEq TyGate TyGate Refl = Yes (Same Refl Refl)

-- [ Connections ]

decEq TyConn TyConn Refl = Yes (Same Refl Refl)

-- [ Ports ]
decEq (TyPort l dx sx wx tx ux) (TyPort l dy sy wy ty uy) Refl = Port.decEq (TyPort l dx sx wx tx ux) (TyPort l dy sy wy ty uy)

decEq (TyModule xs) (TyModule ys) Refl with (Ports.decEq xs ys)
  decEq (TyModule xs) (TyModule xs) Refl | (Yes Refl) = Yes (Same Refl Refl)
  decEq (TyModule xs) (TyModule ys) Refl | (No contra) = No (modBodyDiffer contra)



DecEqIdx MTy Ty where
  decEq x y prf = Equality.decEq x y prf


-- [ EOF ]
