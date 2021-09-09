||| A version of `Dec` that returns a meaningful error message as well as proof of void.
|||
||| When dealing with decidable properties for type-level computations
||| the existing `Dec` data type is useful.  However, when using
||| decidable properties interactively one cannot easily tell why a
||| property failed.  One can always encode failing cases within the
||| property itself but that is not necessarily a advantageous.
|||
||| `DecInfo` provides a data structure to capture decidable properties together with an informative error message for when the property does not hold.
module Toolkit.Decidable.Informative

import Decidable.Equality
%default total


public export
data DecInfo : (errType : Type) -> (prop : Type) -> Type where
   Yes : (prfWhy : prop) -> DecInfo errType prop
   No  : (msgWhyNot : errType) -> (prfWhyNot : prop -> Void) -> DecInfo errType prop


export
otherwise : DecInfo e b -> (a -> b) -> Either (e, Not a) b
otherwise (Yes prfWhy) f = Right prfWhy
otherwise (No msgWhyNot prfWhyNot) f = Left (msgWhyNot, \x => prfWhyNot (f x))

export
try : DecInfo e b -> (a -> b) -> Either (e, Not a) b
try = otherwise

export
decInfoDo : Either (e, Not a) a -> DecInfo e a
decInfoDo (Left (x, y)) = No x y
decInfoDo (Right x) = Yes x

namespace Lift

  export
  otherwise : DecInfo eB b -> (eB -> eA) -> (a -> b) -> Either (eA, Not a) b
  otherwise (Yes prfWhy) _ _ = Right prfWhy
  otherwise (No msgWhyNot prfWhyNot) g f = Left (g msgWhyNot, \x => prfWhyNot (f x))

  export
  try : DecInfo eB b -> (eB -> eA) -> (a -> b) -> Either (eA, Not a) b
  try = otherwise
-- --------------------------------------------------------------------- [ EOF ]
