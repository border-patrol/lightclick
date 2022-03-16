module Toolkit.DeBruijn.Environment

import public Data.List.Elem
import public Toolkit.Data.DList

%default total

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

||| Add an object to our execution environment.
||| @env The typing environment.
export
extend : {t : ty}
      -> (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (t::ctxt)
extend env obj = obj :: env

||| Read an object from our typing environment.
|||
||| @idx Which object.
||| @env The execution environment.
export
read : (idx : Elem t ctxt)
    -> (env : Env ty e ctxt)
    -> e t
read Here      (obj::store) = obj
read (There x) (obj::store) = read x store

||| Add an object to our execution environment.
|||
||| @idx Where the object is.
||| @obj The new object.
||| @env The environment to which the object is added.
export
update : (idx : Elem t ctxt)
      -> (obj : e t)
      -> (env : Env ty e ctxt)
      -> Env ty e ctxt
update Here      obj (_    :: store) = obj  :: store
update (There x) obj (obj' :: store) = obj' :: update x obj store


-- [ EOF ]
