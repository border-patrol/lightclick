module LightClick.Terms

import Data.Vect
import Data.Vect.Elem

import Data.DList
import Data.DList.DeBruijn
import Data.DVect


import Commons.Data.Location

import LightClick.Types
import LightClick.Error

%default total


namespace Context
   public export
   Context : Type
   Context = List (Pair String MTy)

   public export
   Index : Context -> Pair String MTy -> Type
   Index = DeBruijn.Index (Pair String MTy)

namespace Term

  public export
   data Term : (ctxt : Context) -> MTy -> Type where
      Ref : {label : String}
         -> {type  : MTy}
         -> (fc  : FileContext)
         -> (prf : Index ctxt (label,type))
         -> Term ctxt type

      Let : {typeE : MTy}
         -> (fc     : FileContext)
         -> (label  : String)
         -> (this   : Term ctxt typeE)
         -> (inThis : Term ((label,typeE)::ctxt) typeB)
         -> Term ctxt typeB

      Seq : {typeA,typeB : MTy} -> Term ctxt typeA -> Term ctxt typeB -> Term ctxt typeB

      DataLogic : (fc : FileContext) -> Term ctxt DATA

      DataArray : (fc : FileContext) -> (type : Term ctxt DATA) -> (size : Nat) -> Term ctxt DATA

      DataStruct : {n : Nat}
                -> (fc : FileContext)
                -> (xs : Vect (S n) (Pair String (Term ctxt DATA)))
                -> Term ctxt DATA
      DataUnion : {n : Nat}
               -> (fc : FileContext)
               -> (xs : Vect (S n) (Pair String (Term ctxt DATA)))
               -> Term ctxt DATA

      Port : (fc : FileContext)
          -> (l  : String)
          -> (d  : Direction)
          -> (s  : Sensitivity)
          -> (w  : Wire)
          -> (i  : Term ctxt DATA)
          -> Term ctxt (PORT l)

      Module : {n : Nat}
            -> {names : Vect (S n) String}
            -> (fc : FileContext)
            -> (ports : DVect String
                              (\s => Term ctxt (PORT s))
                              (S n)
                              names)
            -> Term ctxt (MODULE names)

      Index : {label : String}
           -> (fc : FileContext)
           -> (mod : Term ctxt (MODULE names))
           -> Elem label names
           -> Term ctxt (PORT label)

      Connect : (fc    : FileContext)
             -> (left  : Term ctxt (PORT a))
             -> (right : Term ctxt (PORT b))
             -> Term ctxt CONN

      FanOut : (fc     : FileContext)
            -> (input  : Term ctxt (PORT s))
            -> (fan : DVect String
                            (\s => Term ctxt (PORT s))
                            (S (S n))
                            names)
            -> Term ctxt CONN

      Mux : {n : Nat}
         -> {c,o : String}
         -> {names : Vect (S (S n)) String}
         -> (fc     : FileContext)
         -> (fan : DVect String
                         (\s => Term ctxt (PORT s))
                         (S (S n))
                         names)
         -> (ctrl   : Term ctxt (PORT c))
         -> (output : Term ctxt (PORT o))
         -> Term ctxt CONN

      End : Term ctxt UNIT

export
getFC : Term ctxt type -> Maybe FileContext
getFC (Ref x y) = Just x
getFC (Let x label this inThis) = Just x
getFC (Seq x y) = Nothing
getFC (DataLogic fc) = Just fc
getFC (DataArray fc type size) = Just fc
getFC (DataStruct fc xs) = Just fc
getFC (DataUnion fc xs) = Just fc
getFC (Port fc l d s w i) = Just fc
getFC (Module fc ports) = Just fc
getFC (Index fc mod x) = Just fc
getFC (Connect fc left right) = Just fc
getFC (FanOut fc input fanOut) = Just fc
getFC (Mux fc fanIn ctrl output) = Just fc
getFC End = Nothing


namespace ErrorFul
 export
 getFC : Term ctxt type -> Either LightClick.Error FileContext
 getFC term =
   case getFC term of
     Nothing => Left (NotSupposedToHappen $ Just "getFC")
     Just fc => Right fc

-- [ EOF ]
