module Toolkit.Data.DList.DeBruijn

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.List.DeBruijn

import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

%default total

namespace DList

  public export
  Context : (idx      : Type)
         -> (type     : idx -> Type)
         -> (indicies : List idx)
                     -> Type
  Context = DList

  public export
  Contains : (idxType  : Type)
          -> (typeType : idxType -> Type)

          -> {indicies : List idxType}

          -> (ctxt : Context idxType typeType indicies)
          -> {idx  : idxType}
          -> (type : typeType idx)
                  -> Type
  Contains idxType typeType xs x = Elem idxType typeType x xs

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : {v : a}
      -> (xs : DList a e vs)
      -> (x  : e v)
            -> DList a e (v::vs)
  (+=) xs x = x :: xs

{- A nice to have below, work in progress.

namespace Renaming

  public export
  weaken : {idx : typeIdx}
        -> {type' : typeType idx}
        -> (func : Contains typeIdx typeType old type
                -> Contains typeIdx typeType new type)
        -> (Contains typeIdx typeType (old += type') type
         -> Contains typeIdx typeType (new += type') type)

  weaken func (H (Same Refl Refl)) = H (Same Refl Refl)
  weaken func (T rest)             = T (func rest)

  public export
  interface Rename (idxType  : Type)
                   (typeType : idxType -> Type)
                   (term     : {indicies : List idxType}
                            -> {idx      : idxType}
                            -> (context  : DList idxType typeType indicies)
                            -> (type     : typeType idx)
                                        -> Type)
      | term
    where

      rename : {indiciesOld : List idxType}
            -> {indiciesNew : List idxType}
            -> {old : DList idxType typeType indiciesOld}
            -> {new : DList idxType typeType indiciesNew}
            -> (f : {level : idxType}
                 -> {type  : typeType level}
                          -> Contains idxType typeType old type
                          -> Contains idxType typeType new type)
           -> ({level : idxType}
            -> {type  : typeType level}
                     -> term old type
                     -> term new type)

      var : {indicies : List idxType}
         -> {ctxt     : DList idxType typeType indicies}
         -> {idx      : idxType}
         -> {type     : typeType idx}
                     -> Elem idxType typeType type ctxt
                     -> term ctxt type

--  weakens : {idxType  : Type}
--         -> {typeType : idxType -> Type}
--         -> {term     : {indicies : List idxType}
--                     -> {idx      : idxType}
--                     -> (context  : DList idxType typeType indicies)
--                     -> (type     : typeType idx)
--                                 -> Type}
--         -> Rename idxType typeType term
--         => {indiciesOld : List idxType}
--         -> {indiciesNew : List idxType}
--         -> {old : DList idxType typeType indiciesOld}
--         -> {new : DList idxType typeType indiciesNew}
--         -> {level' : idxType}
--         -> {type' : typeType level'}
--         -> (f : {level : idxType}
--              -> {type  : typeType level}
--                       -> Contains idxType typeType old type
--                       -> term                      new type)
--         -> ({level : idxType}
--          -> {type  : typeType level}
--                   -> Contains idxType typeType (type' :: old) type
--                   -> term                      (type' :: new) type)
--  weakens f (H (Same Refl Refl)) = var (H (Same Refl Refl))
--  weakens f (T rest)             = rename T (f rest)

namespace Substitution

  namespace General
    public export
    interface Rename idx type term
           => Substitute (idxType  : Type)
                         (typeType : idxType -> Type)
                         (term     : {indicies : List idxType}
                                  -> {idx      : idxType}
                                  -> (context  : DList idxType typeType indicies)
                                  -> (type     : typeType idx)
                                              -> Type)
         | term
       where

         subst : {old, new : List type}
              -> (f : {ty  : type}
                          -> Contains old ty
                          -> term     new ty)
              -> ({ty : type}
                     -> term old ty
                     -> term new ty)
(f : {level : Universe}
            -> {type  : MTy level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : MTy level}
                 -> SystemV old type
                 -> SystemV new type)

--  namespace Single
--
--    apply : {type : Type}
--         -> {term : List type -> type -> Type}
--         -> Rename type term
--         => {ctxt   : List type}
--         -> {typeA  : type}
--         -> {typeB  : type}
--         -> (this   : term      ctxt    typeB)
--         -> (idx    : Contains (ctxt += typeB) typeA)
--                   -> term      ctxt           typeA
--    apply this Here = this
--    apply this (There rest) = var rest
--
--    export
--    subst : {type : Type}
--         -> {term : List type -> type -> Type}
--         -> Rename type term
--         => Substitute type term
--         => {ctxt          : List type}
--         -> {typeA         : type}
--         -> {typeB         : type}
--         -> (this          : term  ctxt           typeB)
--         -> (inThis        : term (ctxt += typeB) typeA)
--                          -> term  ctxt           typeA
--    subst {ctxt} {typeA} {typeB} this inThis
--      = subst (apply this) inThis

-}
-- [ EOF ]
