module Data.DList.Elem

import Data.DList

import public Decidable.Equality.Indexed

%default total

||| Proof that some element is found in a `DList`.
|||
||| @iTy     The type of the element's index.
||| @elemTy  The type of the list element.
||| @x       An element in the list.
||| @xs      The list itself.
||| @prf     Proof that the element's index is in the list in the same position as the element itself.
public export
data Elem : (iTy    : Type)
         -> (elemTy : iTy -> Type)
         -> forall i, is
          . (x      : elemTy i)
         -> (xs     : DList iTy elemTy is)
         -> Type
    where
      ||| Proof that the element is at the front of the list.
      H : (x=y) -> Elem ity elemTy x (y :: xs)

      ||| Proof that the element is found later in the list.
      T : (later : Elem iTy elemTy x       xs)
                -> Elem iTy elemTy x (x' ::xs)

-- [ EOF ]
