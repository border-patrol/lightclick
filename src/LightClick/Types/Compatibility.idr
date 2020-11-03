module LightClick.Types.Compatibility

import public Decidable.Equality.Indexed

import public Toolkit.Decidable.Informative

import Toolkit.Data.Rig
import Toolkit.Data.Vect.Extra

import LightClick.Error

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
    posFlip CompatLogic = CompatLogic


    export
    negFlip : (Data.Compatible l r -> Void) -> Data.Compatible r l -> Void
    negFlip f (CompatArray Refl prf) = f (CompatArray Refl (posFlip prf))
    negFlip f (CompatStruct prfs) = f (CompatStruct (posFlips prfs))
    negFlip f (CompatUnion  prfs) = f (CompatUnion (posFlips prfs))
    negFlip f CompatLogic = f CompatLogic

    export
    posFlips : (Fields.Compatible ls rs) -> Fields.Compatible rs ls
    posFlips Empty = Empty
    posFlips (Cons Refl prf rest) = Cons Refl (posFlip prf) (posFlips rest)



namespace Logic
  export
  logicNotCompatWithArray : Data.Compatible TyLogic (TyArray l t) -> Void
  logicNotCompatWithArray (CompatArray _ _) impossible
  logicNotCompatWithArray (CompatStruct _) impossible
  logicNotCompatWithArray (CompatUnion _) impossible
  logicNotCompatWithArray CompatLogic impossible

  export
  logicNotCompatWithStruct : Data.Compatible TyLogic (TyStruct xs) -> Void
  logicNotCompatWithStruct (CompatArray _ _) impossible
  logicNotCompatWithStruct (CompatStruct _) impossible
  logicNotCompatWithStruct (CompatUnion _) impossible
  logicNotCompatWithStruct CompatLogic impossible


  export
  logicNotCompatWithUnion : Data.Compatible TyLogic (TyUnion xs) -> Void
  logicNotCompatWithUnion (CompatArray _ _) impossible
  logicNotCompatWithUnion (CompatStruct _) impossible
  logicNotCompatWithUnion (CompatUnion _) impossible
  logicNotCompatWithUnion CompatLogic impossible

namespace Array

  export
  arraysNotSameLength : (contra : (k = j) -> Void)
                     -> Data.Compatible (TyArray x k) (TyArray y j)
                     -> Void
  arraysNotSameLength contra (CompatArray prf x) = contra prf

  export
  arraysNotSameType : (f : Data.Compatible x y -> Void)
                   -> Data.Compatible (TyArray x j) (TyArray y j)
                   -> Void
  arraysNotSameType f (CompatArray Refl x) = f x

  export
  arrayNotCompatWithStruct : Data.Compatible (TyArray x k) (TyStruct xs) -> Void
  arrayNotCompatWithStruct (CompatArray _ _) impossible
  arrayNotCompatWithStruct (CompatStruct _) impossible
  arrayNotCompatWithStruct (CompatUnion _) impossible
  arrayNotCompatWithStruct CompatLogic impossible

  export
  arrayNotCompatWithUnion : Data.Compatible (TyArray x k) (TyUnion xs) -> Void
  arrayNotCompatWithUnion (CompatArray _ _) impossible
  arrayNotCompatWithUnion (CompatStruct _) impossible
  arrayNotCompatWithUnion (CompatUnion _ ) impossible
  arrayNotCompatWithUnion CompatLogic impossible

namespace Struct

  export
  structNotCompatWithUnion : Data.Compatible (TyStruct xs) (TyUnion ys) -> Void
  structNotCompatWithUnion (CompatArray _ _) impossible
  structNotCompatWithUnion (CompatStruct _) impossible
  structNotCompatWithUnion (CompatUnion _ ) impossible
  structNotCompatWithUnion CompatLogic impossible

  export
  structsAreNotCompat : (Compatible xs ys -> Void) -> Compatible (TyStruct xs) (TyStruct ys) -> Void
  structsAreNotCompat contra (CompatStruct prf) = contra prf

namespace Union

  export
  unionsAreNotCompat : (Compatible xs ys -> Void) -> Compatible (TyUnion xs) (TyUnion ys) -> Void
  unionsAreNotCompat contra (CompatUnion prf) = contra prf

-- [ Function Declaration ]

export
compatible : (x : Ty DATA)
          -> (y : Ty DATA)
                 -> DecInfo Compatibility.Data.Error
                            (Data.Compatible x y)


namespace Fields
  fieldMismatchLabel : (xl = yl -> Void)
                    -> Fields.Compatible ((xl, xt) :: xs) ((yl, yt) :: ys)
                    -> Void
  fieldMismatchLabel contra (Cons Refl prf rest) = contra Refl

  fieldMismatchType : (Compatible xt yt -> Void)
                   -> Compatible ((xl, xt) :: xs) ((xl, yt) :: ys)
                   -> Void
  fieldMismatchType contra (Cons Refl prf rest) = contra prf

  restNotCompatible : (Compatible xs ys -> Void)
                   -> Compatible ((xl, xt) :: xs) ((xl, yt) :: ys)
                   -> Void
  restNotCompatible contra (Cons Refl prf rest) = contra rest

  fieldsLeftIsLarger : Compatible (x :: xs) [] -> Void
  fieldsLeftIsLarger _ impossible

  fieldsRightIsLarger : Compatible [] (y :: ys) -> Void
  fieldsRightIsLarger _ impossible

  export
  compatible : (kxs : Vect n (Pair String (Ty DATA)))
            -> (kys : Vect m (Pair String (Ty DATA)))
                        -> DecInfo Compatibility.Data.Error
                                   (Fields.Compatible kxs kys)

  compatible {n} xs {m} ys with (shape xs ys)
    compatible {n = 0} [] {m = 0} [] | Empty = Yes Empty


    compatible {n = (S len)} (x :: xs) {m = 0} [] | LH = No MismatchStructureLength fieldsLeftIsLarger
    compatible {n = 0} [] {m = (S len)} (y :: ys) | RH = No MismatchStructureLength fieldsRightIsLarger

    compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((yl, yt) :: ys) | Both with (decEq xl yl)
      compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) with (compatible xt yt)
        compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (Yes prf) with (compatible xs ys)
          compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (Yes prf) | (Yes rest)
            = Yes (Cons Refl prf rest)
            -- End of happy path

          -- Rest not happy somewhere, and need to update position when it is recorded.
          compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (Yes prf) | (No (MismatchStructureFieldType position error) contra)
            = No (MismatchStructureFieldType (S position) error) (restNotCompatible contra)
          compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (Yes prf) | (No (MismatchStructureFieldLabel position x y) contra)
            = No (MismatchStructureFieldLabel (S position) x y) (restNotCompatible contra)
          compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (Yes prf) | (No msg contra)
            = No msg (restNotCompatible contra)


        -- Type mismatch
        compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((xl, yt) :: ys) | Both | (Yes Refl) | (No msg contra)
          = No (MismatchStructureFieldType Z msg) (fieldMismatchType contra)
      -- Label mismatch
      compatible {n = (S len)} ((xl, xt) :: xs) {m = (S len)} ((yl, yt) :: ys) | Both | (No contra)
        = No (MismatchStructureFieldLabel Z xl yl) (fieldMismatchLabel contra)

-- [ Definition Starts Here]

-- [ Logic vs X ]

compatible TyLogic TyLogic = Yes CompatLogic
compatible TyLogic (TyArray l t) = No Mismatch logicNotCompatWithArray
compatible TyLogic (TyStruct kvs) = No Mismatch logicNotCompatWithStruct
compatible TyLogic (TyUnion kvs) = No Mismatch logicNotCompatWithUnion

-- [ Array vs X ]

compatible (TyArray type length) TyLogic = No Mismatch (negFlip logicNotCompatWithArray)

compatible (TyArray typeA lengthA) (TyArray typeB lengthB) with (decEq lengthA lengthB)
  compatible (TyArray typeA lengthA) (TyArray typeB lengthA) | Yes Refl with (compatible typeA typeB)
    compatible (TyArray typeA lengthA) (TyArray typeB lengthA) | Yes Refl | Yes prf
      = Yes (CompatArray Refl prf)

    compatible (TyArray typeA lengthA) (TyArray typeB lengthA) | Yes Refl | No msg contra
      = No (MismatchArrayType msg) (arraysNotSameType contra)
  compatible (TyArray typeA lengthA) (TyArray typeB lengthB) | No contra
    = No MismatchArrayLength (arraysNotSameLength contra)

compatible (TyArray type length) (TyStruct kvs) = No Mismatch arrayNotCompatWithStruct
compatible (TyArray type length) (TyUnion kvs) = No Mismatch arrayNotCompatWithUnion

-- [ Struct vs X ]

compatible (TyStruct kvs) TyLogic
  = No Mismatch (negFlip logicNotCompatWithStruct)

compatible (TyStruct kvs) (TyArray type length)
  = No Mismatch (negFlip arrayNotCompatWithStruct)

compatible (TyStruct xs) (TyStruct ys) with (Fields.compatible xs ys)
  compatible (TyStruct xs) (TyStruct ys) | (Yes prf) = Yes (CompatStruct prf)
  compatible (TyStruct xs) (TyStruct ys) | (No msg contra) = No msg (structsAreNotCompat contra)


compatible (TyStruct kvs) (TyUnion xs) = No Mismatch structNotCompatWithUnion

-- [ Union vs X ]

compatible (TyUnion kvs) TyLogic = No Mismatch (negFlip logicNotCompatWithUnion)

compatible (TyUnion kvs) (TyArray type length) = No Mismatch (negFlip arrayNotCompatWithUnion)

compatible (TyUnion xs) (TyStruct ys) = No Mismatch (negFlip structNotCompatWithUnion)

compatible (TyUnion xs) (TyUnion ys) with (Fields.compatible xs ys)
  compatible (TyUnion xs) (TyUnion ys) | (Yes prf) = Yes (CompatUnion prf)
  compatible (TyUnion xs) (TyUnion ys) | (No msg contra) = No msg (unionsAreNotCompat contra)


-- [ EOF ]
