module LightClick.Types.Compatibility

import public Toolkit.Decidable.Equality.Indexed

import public Toolkit.Decidable.Informative

import Toolkit.Data.Rig
import Toolkit.Data.Vect.Extra

import LightClick.Types.Meta
import LightClick.Types.Direction
import LightClick.Types.Sensitivity
import LightClick.Types.WireType

import LightClick.Types
import LightClick.Types.Equality

%default total


namespace Data

  mutual
    namespace Fields
      public export
      data Compatible : (kxs : Vect n (Pair String (Ty DATA)))
                     -> (kys : Vect m (Pair String (Ty DATA)))
                                 -> Type
        where
          Empty : Compatible Nil Nil
          Cons : (compatLabels :                     i        =  j)
              -> (compatTypes  : Data.Compatible       a           b)
              -> (rest         : Fields.Compatible         xs          ys)
                              -> Fields.Compatible ((i,a)::xs) ((j,b)::ys)

    public export
    data Compatible : (x,y : Ty DATA) -> Type where
      CompatLogic : Data.Compatible TyLogic TyLogic
      CompatEnum  : (prf : xs = ys) -> Data.Compatible (TyEnum xs) (TyEnum ys)
      CompatArray : (sameLength : i = j)
                 -> (types      : Data.Compatible a b)
                               -> Data.Compatible (TyArray a i)
                                                  (TyArray b j)
      CompatStruct : (compatFields : Fields.Compatible xs ys)
                                  -> Data.Compatible (TyStruct xs) (TyStruct ys)
      CompatUnion : (compatFields : Fields.Compatible xs ys)
                                 -> Data.Compatible (TyUnion xs) (TyUnion ys)


    export
    posFlip : Data.Compatible l r -> Data.Compatible r l
    posFlip (CompatArray Refl prf) = CompatArray Refl (posFlip prf)
    posFlip (CompatStruct prfs) = CompatStruct (posFlips prfs)
    posFlip (CompatUnion  prfs) = CompatUnion (posFlips prfs)
    posFlip (CompatEnum Refl) = CompatEnum Refl
    posFlip CompatLogic = CompatLogic


    export
    negFlip : (Data.Compatible l r -> Void) -> Data.Compatible r l -> Void
    negFlip f (CompatArray Refl prf) = f (CompatArray Refl (posFlip prf))
    negFlip f (CompatStruct prfs) = f (CompatStruct (posFlips prfs))
    negFlip f (CompatUnion  prfs) = f (CompatUnion (posFlips prfs))
    negFlip f CompatLogic = f CompatLogic
    negFlip f (CompatEnum Refl) = f (CompatEnum Refl)

    export
    posFlips : (Fields.Compatible ls rs) -> Fields.Compatible rs ls
    posFlips Empty = Empty
    posFlips (Cons Refl prf rest) = Cons Refl (posFlip prf) (posFlips rest)


-- [ Function Declaration & Error ]

namespace Data
  public export
  data Error : Type where
    Mismatch : Data.Error
    MismatchArrayLength : Data.Error
    MismatchArrayType   : (error : Data.Error) -> Data.Error
    MismatchStructureFieldType  : (position : Nat) -> (error : Data.Error) -> Data.Error
    MismatchStructureFieldLabel  : (position : Nat) -> (x,y : String) -> Data.Error
    MismatchStructureLength : Data.Error



export
compatible : (x : Ty DATA)
          -> (y : Ty DATA)
                 -> DecInfo Data.Error
                            (Data.Compatible x y)


fields : (kxs : Vect n (Pair String (Ty DATA)))
      -> (kys : Vect m (Pair String (Ty DATA)))
             -> DecInfo Compatibility.Data.Error
                        (Fields.Compatible kxs kys)

Uninhabited (Data.Compatible TyLogic (TyArray l t)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible TyLogic (TyEnum xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible TyLogic (TyStruct xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible TyLogic (TyUnion xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible (TyEnum xs) (TyArray l t)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible (TyEnum xs) (TyStruct kvs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible (TyEnum xs) (TyUnion kvs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible a b) => Uninhabited (Data.Compatible (TyArray a l) (TyArray b j)) where
  uninhabited (CompatArray sameLength types) = absurd types


Uninhabited (Data.Compatible (TyArray l ty) (TyStruct xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible (TyArray l ty) (TyUnion xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Data.Compatible (TyStruct kvs) (TyUnion xs)) where
  uninhabited CompatLogic impossible

Uninhabited (Compatible (x :: xs) []) where
  uninhabited Empty impossible

Uninhabited (Compatible [] (x :: xs)) where
  uninhabited Empty impossible


fields {n} {m} kxs kys with (shape kxs kys)
  fields {n = 0} {m = 0} [] [] | Empty
    = Yes Empty

  fields {n = (S len)} {m = 0} (x :: xs) [] | LH
    = No MismatchStructureLength absurd
  fields {n = 0} {m = (S len)} [] (y :: ys) | RH
    = No MismatchStructureLength absurd

  fields {n = (S len)} {m = (S len)} ((kx,vx) :: xs) ((ky,vy) :: ys) | Both
    = case decEq kx ky of
        No contra => No (MismatchStructureFieldLabel Z kx ky) (\(Cons Refl prf rest) => contra Refl)
        Yes Refl =>
          case compatible vx vy of
            No msg contra => No (MismatchStructureFieldType Z msg)
                                (\(Cons Refl prf rest) => contra prf)
            Yes prfH =>
              case fields xs ys of
                Yes prfT
                  => Yes (Cons Refl prfH prfT)

                No (MismatchStructureFieldType position error) contra
                  => No (MismatchStructureFieldType (S position) error)
                        (\(Cons Refl prf rest) => contra rest)
                No (MismatchStructureFieldLabel position x y) contra
                  => No (MismatchStructureFieldLabel (S position) x y)
                        (\(Cons Refl prf rest) => contra rest)
                No msg contra
                  => No msg (\(Cons Refl prf rest) => contra rest)

compatible TyLogic TyLogic
  = Yes CompatLogic
compatible TyLogic (TyEnum xs)
  = No Mismatch absurd
compatible TyLogic (TyArray type length)
  = No Mismatch absurd
compatible TyLogic (TyStruct kvs)
  = No Mismatch absurd
compatible TyLogic (TyUnion kvs)
  = No Mismatch absurd

compatible (TyEnum xs) TyLogic
  = No Mismatch (negFlip absurd)
compatible (TyEnum xs) (TyEnum ys)
  = case decEq xs ys of
      No c => No Mismatch (\(CompatEnum Refl) => c Refl)
      Yes Refl => Yes (CompatEnum Refl)

compatible (TyEnum xs) (TyArray type length)
  = No Mismatch absurd
compatible (TyEnum xs) (TyStruct kvs)
  = No Mismatch absurd
compatible (TyEnum xs) (TyUnion kvs)
  = No Mismatch absurd

compatible (TyArray type length) TyLogic
  = No Mismatch (negFlip absurd)
compatible (TyArray type length) (TyEnum xs)
  = No Mismatch (negFlip absurd)
compatible (TyArray type length) (TyArray x k)
  = case compatible type x of
      No msg contra => No (MismatchArrayType msg)
                          (\(CompatArray Refl prf) => contra prf)
      Yes prf =>
        case decEq length k of
          No contra => No (MismatchArrayLength)
                          (\(CompatArray Refl prf) => contra Refl)

          Yes Refl => Yes (CompatArray Refl prf)

compatible (TyArray type length) (TyStruct kvs)
  = No Mismatch absurd
compatible (TyArray type length) (TyUnion kvs)
  = No Mismatch absurd

compatible (TyStruct kvs) TyLogic
  = No Mismatch (negFlip absurd)
compatible (TyStruct kvs) (TyEnum xs)
  = No Mismatch (negFlip absurd)
compatible (TyStruct kvs) (TyArray type length)
  = No Mismatch (negFlip absurd)

compatible (TyStruct kvs) (TyStruct xs)
  = case fields kvs xs of
      No msg contra => No msg (\(CompatStruct prf) => contra prf)
      Yes prf => Yes (CompatStruct prf)

compatible (TyStruct kvs) (TyUnion xs)
  = No Mismatch absurd

compatible (TyUnion kvs) TyLogic
  = No Mismatch (negFlip absurd)
compatible (TyUnion kvs) (TyEnum xs)
  = No Mismatch (negFlip absurd)
compatible (TyUnion kvs) (TyArray type length)
  = No Mismatch (negFlip absurd)
compatible (TyUnion kvs) (TyStruct xs)
  = No Mismatch (negFlip absurd)

compatible (TyUnion kvs) (TyUnion xs)
  = case fields kvs xs of
      No msg contra => No msg (\(CompatUnion prf) => contra prf)
      Yes prf => Yes (CompatUnion prf)

-- [ EOF ]
