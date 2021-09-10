module LightClick.Types.Necessity

import Decidable.Equality

%default total

public export
data Necessity = REQ | OPT


roNot : REQ = OPT -> Void
roNot Refl impossible

export
DecEq Necessity where
  decEq REQ REQ = Yes Refl
  decEq REQ OPT = No roNot
  decEq OPT REQ = No (negEqSym roNot)
  decEq OPT OPT = Yes Refl

-- [ EOF ]
