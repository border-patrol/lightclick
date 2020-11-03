module LightClick.Env

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.DList.DeBruijn
import Toolkit.Data.Location
import Toolkit.Data.Rig
import Toolkit.Decidable.Equality.Indexed

import Language.SystemVerilog.Utilities

import LightClick.Connection
import LightClick.Error

import LightClick.Types
import LightClick.Types.Equality
import LightClick.Types.Usage
import LightClick.Terms

import LightClick.Values

%default total

namespace TheType

   public export
   data TheType : (String, MTy) -> Type where
     MkTheType : (s : String) -> Ty ty -> TheType (s,ty)

   public export
   Equals : {a,b : Pair String MTy}
         -> (x : TheType a)
         -> (y : TheType b)
              -> Type
   Equals = Equals (String,MTy) TheType

   typesDiffer : (Types.Equality.Equals tyA tyB -> Void)
              -> TheType.Equals (MkTheType l tyA) (MkTheType l tyB)
              -> Void
   typesDiffer contra (Same Refl Refl) = contra (Same Refl Refl)

   decEq : (x : TheType a)
        -> (y : TheType b)
        -> (prf : a = b)
        -> Dec (Equals x y)
   decEq (MkTheType l tyA) (MkTheType l tyB) Refl with (decEq tyA tyB Refl)
     decEq (MkTheType l tyA) (MkTheType l tyA) Refl | Yes (Same Refl Refl) = Yes (Same Refl Refl)
     decEq (MkTheType l tyA) (MkTheType l tyB) Refl | No contra = No (typesDiffer contra)

   export
   DecEqIdx (String, MTy) TheType where
     decEq = TheType.decEq

public export
data Entry : Pair String MTy -> Type where
  MkEntry : (value : Value (interp ty))
         -> (type  : TheType (s,ty))
                 -> Entry (s,ty)


public export
Env : Context -> Type
Env = DeBruijn.Env (Pair String MTy) Entry

export
free : Env context -> List (Pair String (List String))
free [] = Nil
free ((MkEntry value (MkTheType name type)) :: rest) with (free type)
  free ((MkEntry value (MkTheType name type)) :: rest) | []
    = free rest
  free ((MkEntry value (MkTheType name type)) :: rest) | (x :: xs)
    = (name,x::xs) :: free rest

-- [ EOF ]
