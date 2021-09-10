module LightClick.Types.Views

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Error

import LightClick.Types
import LightClick.Types.Equality

%default total

public export
data Usage : Ty (PORT l) -> Type where
  Z : Usage (TyPort l d s w t n None)
  O : Usage (TyPort l d s w t n One)
  T : Usage (TyPort l d s w t n Tonne)

export
usage : (p : Ty (PORT l)) -> Usage p
usage (TyPort l d s w t n None) = Z
usage (TyPort l d s w t n One) = O
usage (TyPort l d s w t n Tonne) = T

public export
data Necessity : Ty (PORT l) -> Type where
  REQ : Necessity (TyPort l d s w t REQ u)
  OPT : Necessity (TyPort l d s w t OPT u)

export
necessity : (p : Ty (PORT l)) -> Necessity p
necessity (TyPort l dir sense wty type REQ usage) = REQ
necessity (TyPort l dir sense wty type OPT usage) = OPT

-- [ EOF ]
