module LightClick.Types.WireType

import Decidable.Equality

import Commons.Decidable.Informative

import LightClick.Error

%default total

public export
data Wire : Type where
   Data      : Wire
   Address   : Wire
   Clock     : Wire
   Reset     : Wire
   Info      : Wire
   Interrupt : Wire
   Control   : Wire
   General   : Wire

dataNotAddress : (Data = Address) -> Void
dataNotAddress Refl impossible

dataNotClock : (Data = Clock) -> Void
dataNotClock Refl impossible

dataNotReset : (Data = Reset) -> Void
dataNotReset Refl impossible

dataNotInfo : (Data = Info) -> Void
dataNotInfo Refl impossible

dataNotInterrupt : (Data = Interrupt) -> Void
dataNotInterrupt Refl impossible

dataNotControl : (Data = Control) -> Void
dataNotControl Refl impossible

dataNotGeneral : (Data = General) -> Void
dataNotGeneral Refl impossible

addressNotClock : (Address = Clock) -> Void
addressNotClock Refl impossible

addressNotReset : (Address = Reset) -> Void
addressNotReset Refl impossible

addressNotInfo : (Address = Info) -> Void
addressNotInfo Refl impossible

addressNotInterrupt : (Address = Interrupt) -> Void
addressNotInterrupt Refl impossible

addressNotControl : (Address = Control) -> Void
addressNotControl Refl impossible

addressNotGeneral : (Address = General) -> Void
addressNotGeneral Refl impossible

clockNotReset : (Clock = Reset) -> Void
clockNotReset Refl impossible

clockNotInfo : (Clock = Info) -> Void
clockNotInfo Refl impossible

clockNotInterrupt : (Clock = Interrupt) -> Void
clockNotInterrupt Refl impossible

clockNotControl : (Clock = Control) -> Void
clockNotControl Refl impossible

clockNotGeneral : (Clock = General) -> Void
clockNotGeneral Refl impossible

resetNotInfo : (Reset = Info) -> Void
resetNotInfo Refl impossible

resetNotInterrupt : (Reset = Interrupt) -> Void
resetNotInterrupt Refl impossible

resetNotControl : (Reset = Control) -> Void
resetNotControl Refl impossible

resetNotGeneral : (Reset = General) -> Void
resetNotGeneral Refl impossible

infoNotInterrupt : (Info = Interrupt) -> Void
infoNotInterrupt Refl impossible

infoNotControl : (Info = Control) -> Void
infoNotControl Refl impossible

infoNotGeneral : (Info = General) -> Void
infoNotGeneral Refl impossible

interruptNotControl : (Interrupt = Control) -> Void
interruptNotControl Refl impossible

interruptNotGeneral : (Interrupt = General) -> Void
interruptNotGeneral Refl impossible

controlNotGeneral : (Control = General) -> Void
controlNotGeneral Refl impossible

export
DecEq Wire where
  decEq Data Data = Yes Refl
  decEq Data Address = No dataNotAddress
  decEq Data Clock = No dataNotClock
  decEq Data Reset = No dataNotReset
  decEq Data Info = No dataNotInfo
  decEq Data Interrupt = No dataNotInterrupt
  decEq Data Control = No dataNotControl
  decEq Data General = No dataNotGeneral

  decEq Address Data = No (negEqSym dataNotAddress)
  decEq Address Address = Yes Refl
  decEq Address Clock = (No addressNotClock)
  decEq Address Reset = (No addressNotReset)
  decEq Address Info = (No addressNotInfo)
  decEq Address Interrupt = (No addressNotInterrupt)
  decEq Address Control = (No addressNotControl)
  decEq Address General = (No addressNotGeneral)

  decEq Clock Data = No (negEqSym dataNotClock)
  decEq Clock Address = No (negEqSym addressNotClock)
  decEq Clock Clock = Yes Refl
  decEq Clock Reset = No clockNotReset
  decEq Clock Info = No clockNotInfo
  decEq Clock Interrupt = No clockNotInterrupt
  decEq Clock Control = No clockNotControl
  decEq Clock General = No clockNotGeneral

  decEq Reset Data = No (negEqSym dataNotReset)
  decEq Reset Address = No (negEqSym addressNotReset)
  decEq Reset Clock = No (negEqSym clockNotReset)
  decEq Reset Reset = Yes Refl
  decEq Reset Info = No resetNotInfo
  decEq Reset Interrupt = No resetNotInterrupt
  decEq Reset Control = No resetNotControl
  decEq Reset General = No resetNotGeneral

  decEq Info Data = No (negEqSym dataNotInfo)
  decEq Info Address = No (negEqSym addressNotInfo)
  decEq Info Clock = No (negEqSym clockNotInfo)
  decEq Info Reset = No (negEqSym resetNotInfo)
  decEq Info Info = Yes Refl
  decEq Info Interrupt = No infoNotInterrupt
  decEq Info Control = No infoNotControl
  decEq Info General = No infoNotGeneral

  decEq Interrupt Data = No (negEqSym dataNotInterrupt)
  decEq Interrupt Address = No (negEqSym addressNotInterrupt)
  decEq Interrupt Clock = No (negEqSym clockNotInterrupt)
  decEq Interrupt Reset = No (negEqSym resetNotInterrupt)
  decEq Interrupt Info = No (negEqSym infoNotInterrupt)
  decEq Interrupt Interrupt = Yes Refl
  decEq Interrupt Control = No interruptNotControl
  decEq Interrupt General = No interruptNotGeneral

  decEq Control Data = No (negEqSym dataNotControl)
  decEq Control Address = No (negEqSym addressNotControl)
  decEq Control Clock = No (negEqSym clockNotControl)
  decEq Control Reset = No (negEqSym resetNotControl)
  decEq Control Info = No (negEqSym infoNotControl)
  decEq Control Interrupt = No (negEqSym interruptNotControl)
  decEq Control Control = Yes Refl
  decEq Control General = No controlNotGeneral

  decEq General Data = No (negEqSym dataNotGeneral)
  decEq General Address = No (negEqSym addressNotGeneral)
  decEq General Clock = No (negEqSym clockNotGeneral)
  decEq General Reset = No (negEqSym resetNotGeneral)
  decEq General Info = No (negEqSym infoNotGeneral)
  decEq General Interrupt = No (negEqSym interruptNotGeneral)
  decEq General Control = No (negEqSym controlNotGeneral)
  decEq General General = Yes Refl

public export
data Compatible : (l,r : Wire) -> Type
  where
    SameWire : Compatible w       w
    GAny     : Compatible General a
    AnyG     : Compatible a       General


negCompatibleSym : (Compatible l r -> Void) -> Compatible r l -> Void
negCompatibleSym f SameWire = f SameWire
negCompatibleSym f GAny = f AnyG
negCompatibleSym f AnyG = f GAny


daNotCompat : Compatible Data Address -> Void
daNotCompat SameWire impossible
daNotCompat GAny impossible
daNotCompat AnyG impossible

dcNotCompat : Compatible Data Clock -> Void
dcNotCompat SameWire impossible
dcNotCompat GAny impossible
dcNotCompat AnyG impossible

drNotCompat : Compatible Data Reset -> Void
drNotCompat SameWire impossible
drNotCompat GAny impossible
drNotCompat AnyG impossible

ddNotCompat : Compatible Data Info -> Void
ddNotCompat SameWire impossible
ddNotCompat GAny impossible
ddNotCompat AnyG impossible

diNotCompat : Compatible Data Interrupt -> Void
diNotCompat SameWire impossible
diNotCompat GAny impossible
diNotCompat AnyG impossible

dctrlNotCompat : Compatible Data Control -> Void
dctrlNotCompat SameWire impossible
dctrlNotCompat GAny impossible
dctrlNotCompat AnyG impossible

acNotCompat : Compatible Address Clock -> Void
acNotCompat SameWire impossible
acNotCompat GAny impossible
acNotCompat AnyG impossible

arNotCompat : Compatible Address Reset -> Void
arNotCompat SameWire impossible
arNotCompat GAny impossible
arNotCompat AnyG impossible

aiNotCompat : Compatible Address Info -> Void
aiNotCompat SameWire impossible
aiNotCompat GAny impossible
aiNotCompat AnyG impossible

aitNotCompat : Compatible Address Interrupt -> Void
aitNotCompat SameWire impossible
aitNotCompat GAny impossible
aitNotCompat AnyG impossible

actrlNotCompat : Compatible Address Control -> Void
actrlNotCompat SameWire impossible
actrlNotCompat GAny impossible
actrlNotCompat AnyG impossible

crNotCompat : Compatible Clock Reset -> Void
crNotCompat SameWire impossible
crNotCompat GAny impossible
crNotCompat AnyG impossible

ciNotCompat : Compatible Clock Info -> Void
ciNotCompat SameWire impossible
ciNotCompat GAny impossible
ciNotCompat AnyG impossible

cintNotCompat : Compatible Clock Interrupt -> Void
cintNotCompat SameWire impossible
cintNotCompat GAny impossible
cintNotCompat AnyG impossible

ccNotCompatc : Compatible Clock Control -> Void
ccNotCompatc SameWire impossible
ccNotCompatc GAny impossible
ccNotCompatc AnyG impossible

riNotCompat : Compatible Reset Info -> Void
riNotCompat SameWire impossible
riNotCompat GAny impossible
riNotCompat AnyG impossible

rintNotCompat : Compatible Reset Interrupt -> Void
rintNotCompat SameWire impossible
rintNotCompat GAny impossible
rintNotCompat AnyG impossible

rcNotCompat : Compatible Reset Control -> Void
rcNotCompat SameWire impossible
rcNotCompat GAny impossible
rcNotCompat AnyG impossible

infoINotCompat : Compatible Info Interrupt -> Void
infoINotCompat SameWire impossible
infoINotCompat GAny impossible
infoINotCompat AnyG impossible

infoCNotCompat : Compatible Info Control -> Void
infoCNotCompat SameWire impossible
infoCNotCompat GAny impossible
infoCNotCompat AnyG impossible

interCNotCompat : Compatible Interrupt Control -> Void
interCNotCompat SameWire impossible
interCNotCompat GAny impossible
interCNotCompat AnyG impossible

export
compatible : (l,r : Wire) -> DecInfo Compatibility.Wire.Error (Compatible l r)
compatible Data Data = Yes SameWire
compatible Data Address = No TypesDiffer daNotCompat
compatible Data Clock = No TypesDiffer dcNotCompat
compatible Data Reset = No TypesDiffer drNotCompat
compatible Data Info = No TypesDiffer ddNotCompat
compatible Data Interrupt = No TypesDiffer diNotCompat
compatible Data Control = No TypesDiffer dctrlNotCompat
compatible Data General = Yes AnyG
compatible Address Data = No TypesDiffer $ negCompatibleSym daNotCompat
compatible Address Address = Yes SameWire
compatible Address Clock = No TypesDiffer acNotCompat
compatible Address Reset = No TypesDiffer arNotCompat
compatible Address Info = No TypesDiffer aiNotCompat
compatible Address Interrupt = No TypesDiffer aitNotCompat
compatible Address Control = No TypesDiffer actrlNotCompat
compatible Address General = Yes AnyG
compatible Clock Data = No TypesDiffer (negCompatibleSym dcNotCompat)
compatible Clock Address = No TypesDiffer (negCompatibleSym acNotCompat)
compatible Clock Clock = Yes SameWire
compatible Clock Reset = No TypesDiffer crNotCompat
compatible Clock Info = No TypesDiffer ciNotCompat
compatible Clock Interrupt = No TypesDiffer cintNotCompat
compatible Clock Control = No TypesDiffer ccNotCompatc
compatible Clock General = Yes AnyG
compatible Reset Data = No TypesDiffer (negCompatibleSym drNotCompat)
compatible Reset Address = No TypesDiffer (negCompatibleSym arNotCompat)
compatible Reset Clock = No TypesDiffer (negCompatibleSym crNotCompat)
compatible Reset Reset = Yes SameWire
compatible Reset Info = No TypesDiffer riNotCompat
compatible Reset Interrupt = No TypesDiffer rintNotCompat
compatible Reset Control = No TypesDiffer rcNotCompat
compatible Reset General = Yes AnyG
compatible Info Data = No TypesDiffer (negCompatibleSym ddNotCompat)
compatible Info Address = No TypesDiffer (negCompatibleSym aiNotCompat)
compatible Info Clock = No TypesDiffer (negCompatibleSym ciNotCompat)
compatible Info Reset = No TypesDiffer (negCompatibleSym riNotCompat)
compatible Info Info = Yes SameWire
compatible Info Interrupt = No TypesDiffer infoINotCompat
compatible Info Control = No TypesDiffer infoCNotCompat
compatible Info General = Yes AnyG
compatible Interrupt Data = No TypesDiffer (negCompatibleSym diNotCompat)
compatible Interrupt Address = No TypesDiffer (negCompatibleSym aitNotCompat)
compatible Interrupt Clock = No TypesDiffer (negCompatibleSym cintNotCompat)
compatible Interrupt Reset = No TypesDiffer (negCompatibleSym rintNotCompat)
compatible Interrupt Info = No TypesDiffer (negCompatibleSym infoINotCompat)
compatible Interrupt Interrupt = Yes SameWire
compatible Interrupt Control = No TypesDiffer interCNotCompat
compatible Interrupt General = Yes AnyG
compatible Control Data = No TypesDiffer (negCompatibleSym dctrlNotCompat)
compatible Control Address = No TypesDiffer (negCompatibleSym actrlNotCompat)
compatible Control Clock = No TypesDiffer (negCompatibleSym ccNotCompatc)
compatible Control Reset = No TypesDiffer (negCompatibleSym rcNotCompat)
compatible Control Info = No TypesDiffer (negCompatibleSym infoCNotCompat)
compatible Control Interrupt = No TypesDiffer (negCompatibleSym interCNotCompat)
compatible Control Control = Yes SameWire
compatible Control General = Yes AnyG
compatible General r = Yes GAny


-- [ EOF ]
