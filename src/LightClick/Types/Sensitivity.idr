module LightClick.Types.Sensitivity

import Decidable.Equality

import Toolkit.Decidable.Informative

%default total


||| Capture wire sensitivity
public export
data Sensitivity = High | Low | Rising | Falling | Insensitive

highNotLow : (High = Low) -> Void
highNotLow Refl impossible

highNotRising : (High = Rising) -> Void
highNotRising Refl impossible

highNotFalling : (High = Falling) -> Void
highNotFalling Refl impossible

highNotInsenitive : (High = Insensitive) -> Void
highNotInsenitive Refl impossible

lowNotRising : (Low = Rising) -> Void
lowNotRising Refl impossible

lowNotFalling : (Low = Falling) -> Void
lowNotFalling Refl impossible

lowNotInsensitive : (Low = Insensitive) -> Void
lowNotInsensitive Refl impossible

risingNotFalling : (Rising = Falling) -> Void
risingNotFalling Refl impossible

risingNotInsensitive : (Rising = Insensitive) -> Void
risingNotInsensitive Refl impossible

fallingNotInsensitive : (Falling = Insensitive) -> Void
fallingNotInsensitive Refl impossible

export
DecEq Sensitivity where
  decEq High High        = Yes Refl
  decEq High Low         = No highNotLow
  decEq High Rising      = No highNotRising
  decEq High Falling     = No highNotFalling
  decEq High Insensitive = No highNotInsenitive

  decEq Low High        = No (negEqSym highNotLow)
  decEq Low Low         = Yes Refl
  decEq Low Rising      = No lowNotRising
  decEq Low Falling     = No lowNotFalling
  decEq Low Insensitive = No lowNotInsensitive

  decEq Rising High        = No (negEqSym highNotRising)
  decEq Rising Low         = No (negEqSym lowNotRising)
  decEq Rising Rising      = Yes Refl
  decEq Rising Falling     = No risingNotFalling
  decEq Rising Insensitive = No risingNotInsensitive

  decEq Falling High        = No (negEqSym highNotFalling)
  decEq Falling Low         = No (negEqSym lowNotFalling)
  decEq Falling Rising      = No (negEqSym risingNotFalling)
  decEq Falling Falling     = Yes Refl
  decEq Falling Insensitive = No fallingNotInsensitive

  decEq Insensitive High        = No (negEqSym highNotInsenitive)
  decEq Insensitive Low         = No (negEqSym lowNotInsensitive)
  decEq Insensitive Rising      = No (negEqSym risingNotInsensitive)
  decEq Insensitive Falling     = No (negEqSym fallingNotInsensitive)
  decEq Insensitive Insensitive = Yes Refl

public export
data Compatible : (l,r : Sensitivity) -> Type
  where
    SameSense : Compatible a a
    ToInsense : Compatible a Insensitive
    FoInsense : Compatible Insensitive a

negCompatibleSym : (Compatible l r -> Void) -> Compatible r l -> Void
negCompatibleSym f SameSense = f SameSense
negCompatibleSym f ToInsense = f FoInsense
negCompatibleSym f FoInsense = f ToInsense

noHL : Compatible High Low -> Void
noHL SameSense impossible
noHL ToInsense impossible
noHL FoInsense impossible

noHF : Compatible High Falling -> Void
noHF SameSense impossible
noHF ToInsense impossible
noHF FoInsense impossible

noHR : Compatible High Rising -> Void
noHR SameSense impossible
noHR ToInsense impossible
noHR FoInsense impossible

noLR : Compatible Low Rising -> Void
noLR SameSense impossible
noLR ToInsense impossible
noLR FoInsense impossible

noLF : Compatible Low Falling -> Void
noLF SameSense impossible
noLF ToInsense impossible
noLF FoInsense impossible

noRF : Compatible Rising Falling -> Void
noRF SameSense impossible
noRF ToInsense impossible
noRF FoInsense impossible

namespace Compatibility
  namespace Sensitivity
    public export
    data Error = NoChangeFromHigh
               | NoChangeFromLow
               | NoChangeFromRising
               | NoChangeFromFalling
export
compatible : (l,r : Sensitivity) -> DecInfo Compatibility.Sensitivity.Error (Compatible l r)
compatible High High = Yes SameSense
compatible Low Low = Yes SameSense
compatible Rising Rising = Yes SameSense
compatible Falling Falling = Yes SameSense
compatible Insensitive Insensitive = Yes SameSense
compatible Insensitive b = Yes FoInsense
compatible a Insensitive = Yes ToInsense

compatible High Low     = No NoChangeFromHigh noHL
compatible High Rising  = No NoChangeFromHigh noHR
compatible High Falling = No NoChangeFromHigh noHF

compatible Low High     = No NoChangeFromLow (negCompatibleSym noHL)
compatible Low Rising   = No NoChangeFromLow noLR
compatible Low Falling  = No NoChangeFromLow noLF

compatible Rising High    = No NoChangeFromRising (negCompatibleSym noHR)
compatible Rising Low     = No NoChangeFromRising (negCompatibleSym noLR)
compatible Rising Falling = No NoChangeFromRising noRF

compatible Falling High   = No NoChangeFromFalling (negCompatibleSym noHF)
compatible Falling Low    = No NoChangeFromFalling (negCompatibleSym noLF)
compatible Falling Rising = No NoChangeFromFalling (negCompatibleSym noRF)


-- [ EOF ]
