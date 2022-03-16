module Toolkit.DeBruijn.Renaming

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.DList

%default total

-- A reverse cons operator.
infixr 6 +=

namespace List

  ||| A De Bruijn Index.
  |||
  ||| Future work will be to make this an efficient nameless representation using `AtIndex`.
  |||
  public export
  Contains : List kind -> kind -> Type
  Contains types type = Elem type types

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs


public export
weaken : (func : Contains old type
              -> Contains new type)
      -> (Contains (old += type') type
       -> Contains (new += type') type)

weaken func Here = Here
weaken func (There rest) = There (func rest)

public export
interface Rename (type : Type) (term : List type -> type -> Type) | term where
  rename : {old, new : List type}
        -> (f : {ty : type} -> Contains old ty
                            -> Contains new ty)
        -> ({ty : type} -> term old ty
                        -> term new ty)

  var : {ty   : type}
     -> {ctxt : List type}
             -> Elem ty ctxt
             -> term ctxt ty


  weakens : {old, new : List type}
         -> (f : {ty  : type}
                     -> Contains old ty
                     -> term     new ty)
         -> ({ty,type' : type}
                -> Contains (old += type') ty
                -> term     (new += type') ty)
  weakens f Here = var Here
  weakens f (There rest) = rename There (f rest)

-- [ EOF ]
