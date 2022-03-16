module Toolkit.DeBruijn.Context

import Decidable.Equality

import Data.List.Elem

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Do

import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem
import public Toolkit.Data.DList.Any

%default total

public export
data Error e = NotSatisfied e
             | NotFound


||| An item in our context, paramterised by the type collected.
|||
||| @kind the type of the datatype describing types
||| @type the instance of the type being recorded.
public export
data Item : (kind : Type)
         -> (type : kind)
                 -> Type
  where
    I : (name : String)
     -> (type : kind)
             -> Item kind type

||| A generic container to capture properties over items in the
||| context.
public export
data Holds : (kind : Type)
          -> (pred : {type : kind} -> (item : Item kind type) -> Type)
          -> {type : kind}
          -> (item : Item kind type)
                  -> Type
  where
    H : {pred : {type : kind} -> (item : Item kind type) -> Type}
     -> {i    : kind}
     -> {item : Item kind i}
     -> (prf  : pred item)
             -> Holds kind pred item

||| Does the given predicate hold over the context item
holds : {pred : {type : kind} -> (item : Item kind type) -> Type}
     -> (func : {type : kind} -> (item : Item kind type) -> DecInfo err (pred item))
     -> {type : kind}
     -> (item : Item kind type)
             -> DecInfo (Error err)
                        (Holds kind pred item)
holds f i with (f i)
  holds f i | (Yes prfWhy)
    = Yes (H prfWhy)
  holds f i | (No msg contra)
    = No (NotSatisfied msg)
         (\(H prf) => contra prf)


public export
Context : (kind : Type) -> (types : List kind) -> Type
Context kind = DList kind (Item kind)

public export
extend : (ctxt  : Context kind kinds)
      -> (label : String)
      -> (type  : kind)
               -> Context kind (type::kinds)
extend ctxt l type = I l type :: ctxt

||| A quantifier over the context that the given predicate holds.
|||
||| This is modelled after De Bruijn indices, and the underlying quantifier is `Any`.
|||
||| We will make it nameless later on, as if we try now the indicies are not sufficiently linked to prove false.
public export
data Exists : {kind : Type}
          -> {types : List kind}
          -> (pred : {type : kind} -> (item : Item kind type) -> Type)
           -> (ctxt : Context kind types)
                   -> Type
  where
    B : {pred : {type : kind} -> (item : Item kind type) -> Type}
     -> {ctxt : Context kind types}
     -> {type : kind}
     -> (item : Item kind type)
     -> (prfP : pred item)
     -> (prfE : Any  kind (Item kind) (Holds kind pred) ctxt)
             -> Exists pred ctxt

contextEmpty : {p : {type : kind} -> (item : Item kind type) -> Type}
            -> Exists p [] -> Void
contextEmpty (B _ _ (H prf)) impossible
contextEmpty (B _ _ (T contra later)) impossible


errFound : {p : {type : kind} -> (item : Item kind type) -> Type}
        -> (Exists p rest -> Void)
        -> (Holds kind p item -> Void)
        -> Exists p (item :: rest) -> Void
errFound f g (B (I name type) prfP (H prf))  = g prf
errFound f _ (B (I name type) prfP (T contra later)) = f (B (I name type) prfP later)

||| Does the given variable exist in the context and satisfy the given predicate.
export
exists : {kind : Type}
      -> {err  : Type}
      -> {types : List kind}
      -> {pred : {type : kind} -> (item : Item kind type) -> Type}
      -> (func : {type : kind} -> (item : Item kind type) -> DecInfo err (pred item))
      -> (ctxt : Context kind types)
              -> DecInfo (Error err)
                         (Exists pred ctxt)
exists func []
  = No NotFound
       (contextEmpty)

exists func (elem :: rest) with (holds func elem)
  exists func (elem :: rest) | (Yes (H prf))
    = Yes (B elem prf (H (H prf)))

  exists func (elem :: rest) | (No msgWhyNot prfWhyNot) with (exists func rest)
    exists func (elem :: rest) | (No msgWhyNot prfWhyNot) | (Yes (B item prfP prfE))
      = Yes (B item prfP (T prfWhyNot prfE))
    exists func (elem :: rest) | (No msgWhyNot prfWhyNot) | (No x f)
      = No x (errFound f prfWhyNot)


public export
data Nameless : {kind : Type}
             -> {types : List kind}
             -> (pred : {type : kind} -> (item : Item kind type) -> Type)
             -> (ctxt : Context kind types)
                     -> Type
  where
    N : {pred : {type : kind} -> (item : Item kind type) -> Type}
     -> {ctxt : Context kind types}
     -> (item : Item kind type)
     -> (prf  : pred item)
     -> (idx  : Elem type types)
             -> Nameless pred ctxt

deBruijn : {kind : Type}
        -> {types : List kind}
        -> {pred : {type : kind} -> (item : Item kind type) -> Type}
        -> {ctxt : Context kind types}
        -> (prf  : Any  kind (Item kind) (Holds kind pred) ctxt)
                -> Nameless pred ctxt
deBruijn (H (H prf)) = N _ prf Here

deBruijn (T contra later) with (deBruijn later)
  deBruijn (T contra later) | (N item prf idx)
    = N item prf (There idx)

||| Given a named DeBruijn index make it nameless.
|||
||| Future work will be to make this an efficient nameless representation using `AtIndex`.
export
mkNameless : {kind : Type}
          -> {types : List kind}
          -> {pred : {type : kind} -> (item : Item kind type) -> Type}
          -> {ctxt : Context kind types}
          -> (prf  : Exists   pred ctxt)
                  -> Nameless pred ctxt
mkNameless (B item prfP prfE) = deBruijn prfE


namespace Named

  public export
  data IsBound : (str  : String)
              -> {type : kind}
              -> (item : Item kind type)
                      -> Type
    where
      IsName : (prf : x = y)
                   -> IsBound x (I y type)

  isBound' : (str  : String)
          -> (item : Item kind type)
                  -> DecInfo () (IsBound str item)
  isBound' str (I name type) with (decEq str name)
    isBound' str (I str type) | (Yes Refl)
      = Yes (IsName Refl)

    isBound' str (I name type) | (No contra)
      = No () (\(IsName Refl) => contra Refl)


  isNotBound : {kind : Type}
            -> {types : List kind}
            -> {ctxt : Context kind types}
            -> (Exists (IsBound str) ctxt -> Void)
            ->  Exists (IsBound str) ctxt -> Void
  isNotBound f = f

  export
  isBound : {kind : Type}
         -> {types : List kind}
         -> (str  : String)
         -> (ctxt : Context kind types)
                 -> DecInfo (Error ())
                            (Exists (IsBound str) ctxt)
  isBound str ctxt with (exists (isBound' str) ctxt)
    isBound str ctxt | (Yes prf)
      = Yes prf
    isBound str ctxt | (No _ contra)
      = No NotFound (isNotBound contra)

namespace Result

  public export
  data Result : (kind  : Type)
             -> (term  : (ctxt : List kind) -> (type : kind) -> Type)
             -> (types : List kind)
                      -> Type
    where
      R : (ctxt : Context kind types)
       -> (type : kind)
       -> (inst : term types type)
               -> Result kind term types

  public export
  data View : (kind  : Type)
           -> (term  : (ctxt : List kind) -> (type : kind) -> Type)
           -> (v     : kind -> Type)
           -> {types : List kind}
           -> (res   : Result kind term types)
                   -> Type where

    V : {ctxt : Context kind types}
     -> {inst : term types type}
     -> (prf  : v type)
             -> View kind term v (R ctxt type inst)

  export
  view : {kind  : Type}
      -> {types : List kind}
      -> {term  : (ctxt : List kind) -> (type : kind) -> Type}
      -> {v     : (type : kind) -> Type}
      -> (f     : (type : kind) -> v type)
      -> (res   : Result kind term types)
             -> View kind term v res
  view f (R ctxt type inst) with (f type)
    view f (R ctxt type inst) | res = V res

-- [ EOF ]
