module LightClick.Types.Necessity

import Decidable.Equality

%default total

public export
data Necessity = Required | Optional

Uninhabited (Required = Optional) where
  uninhabited Refl impossible

export
DecEq Necessity where
  decEq Required Required
    = Yes Refl

  decEq Required Optional
    = No absurd

  decEq Optional Required
    = No (negEqSym absurd)

  decEq Optional Optional
    = Yes Refl

-- [ EOF ]
