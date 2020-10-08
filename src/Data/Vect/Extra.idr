module Data.Vect.Extra

import public Decidable.Equality
import        Data.Vect

%default total

namespace Equality
   public export
   vecEq : Eq type => Vect n type -> Vect m type -> Bool
   vecEq [] [] = True
   vecEq [] (x :: xs) = False
   vecEq (x :: xs) [] = False
   vecEq (x :: xs) (y :: ys) = x == y && vecEq xs ys

namespace Decidable
  namespace SameLength
    public export
    decEq : DecEq type
          => (n = m)
          -> (xs : Vect n type)
          -> (ys : Vect m type)
          -> Dec (xs = ys)
    decEq Refl xs ys with (decEq xs ys)
      decEq Refl ys ys | (Yes Refl) = Yes Refl
      decEq Refl xs ys | (No contra) = No contra

  namespace DiffLength

    public export
    vectorsDiffLength : DecEq type
                      => (contra : (n = m) -> Void)
                      -> {xs : Vect n type}
                      -> {ys : Vect m type}
                      -> (xs = ys) -> Void
    vectorsDiffLength contra Refl = contra Refl

    public export
    decEq : DecEq type
         => {n,m : Nat}
         -> (xs : Vect n type)
         -> (ys : Vect m type)
         -> Dec (xs = ys)
    decEq xs ys {n} {m} with (decEq n m)
      decEq xs ys {n = m} {m = m} | (Yes Refl) = decEq Refl xs ys
      decEq xs ys {n = n} {m = m} | (No contra) = No (vectorsDiffLength contra)

namespace Shape

  public export
  data Shape : (xs : Vect n a)
            -> (ys : Vect m a)
            -> Type
    where
      Empty : Shape Nil Nil
      LH    : Shape (x::xs) Nil
      RH    : Shape Nil      (y::ys)
      Both  : Shape (x::xs) (y::ys)

  export
  shape : (xs : Vect n a)
       -> (ys : Vect m a)
       -> Shape xs ys
  shape [] [] = Empty
  shape [] (y :: ys) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = Both

-- [ EOF ]
