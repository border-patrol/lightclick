-- ------------------------------------------------------------ [ DeBruijn.idr ]
-- Module    : DeBruijn.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Data structure to compute de Bruijn indices.
|||
||| Thanks to christiansen's Galois tutorials for the accessor and
||| mutator functions for environments/object store.
module Toolkit.Data.DList.DeBruijn

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.DList

%default total



||| A de Bruijn Index.
|||
||| @T    The type of type's collected.
||| @ctxt The collection of types.
||| @t    The element collected at the current position.
public export
Index : (type : Type)
     -> (ctxt : List type)
     -> (t    : type)
             -> Type
Index _ ctxt t = Elem t ctxt


||| Sometimes it is bettern to think that we have this thing called an
||| environment and not a `DList`.
|||
||| @t    The Type for Types in our environment.
||| @obj  How we interpret the types in our DSL. Either this is a
|||       dependent type or a function that computes a type.
||| @ctxt The typing context.
public export
Env : (t : Type) -> (obj : t -> Type) -> (ctxt : List t) -> Type
Env ty obj ctxt = DList ty obj ctxt

||| Add an object from our typing environment.
||| @env The typing environment.
export
extend : {t : ty}
      -> (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (t::ctxt)
extend env obj = obj :: env

||| Read an object from our typing environment.
|||
||| @idx The typing context.
||| @env The typing environment.
export
read : (idx : Index ty ctxt t)
    -> (env : Env ty e ctxt)
    -> e t
read Here      (obj::store) = obj
read (There x) (obj::store) = read x store

||| Add an object to our typnig environment.
|||
||| @idx The typing context.
||| @obj The object to add.
||| @env The environment to which the object is added.
export
update : (idx : Index ty ctxt t )
      -> (obj : e t)
      -> (env : Env ty e ctxt)
      -> Env ty e ctxt
update Here      obj (_    :: store) = obj  :: store
update (There x) obj (obj' :: store) = obj' :: update x obj store

namespace KV


  public export
  indexEmpty : DecEq type
           => (t ** Index (String, type) [] (k, t))
           -> Void
  indexEmpty (MkDPair _ Here) impossible
  indexEmpty (MkDPair _ (There _)) impossible


  public export
  notInIndex : DecEq type
           => (keyContra : (k = a) -> Void)
           -> (index     : List (String, type))
           -> (kvContra  : (t : type ** Index (String, type) xs (k, t)) -> Void)
           -> (prf       : (t : type ** Index (String, type) ((a, b) :: xs) (k, t)))
                        -> Void
  notInIndex keyContra index kvContra (MkDPair b Here) = keyContra Refl
  notInIndex keyContra index kvContra (MkDPair fst (There x)) = kvContra (_ ** x)

  public export
  isIndex : DecEq type
         => (k : String)
         -> (ctxt : List (String, type))
         -> Dec (t : type ** Index (String, type) ctxt (k,t))
  isIndex k [] = No indexEmpty
  isIndex k ((a,b) :: xs) with (decEq k a)
    isIndex a ((a,b) :: xs) | (Yes Refl) = Yes (b ** Here)
    isIndex k ((a,b) :: xs) | (No contra) with (isIndex k xs)
      isIndex k ((a,b) :: xs) | (No contra) | (Yes (MkDPair fst snd))
        = Yes (_ ** There snd)
      isIndex k ((a,b) :: xs) | (No contra) | (No f) = No (notInIndex contra xs f)

-- --------------------------------------------------------------------- [ EOF ]
