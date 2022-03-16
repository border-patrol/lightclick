module Toolkit.DeBruijn.Substitution

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.DList

import Toolkit.DeBruijn.Renaming

%default total


namespace General
  public export
  interface Rename type term
         => Substitute (type : Type) (term : List type -> type -> Type) | term where

    subst : {old, new : List type}
         -> (f : {ty  : type}
                     -> Contains old ty
                     -> term     new ty)
         -> ({ty : type}
                -> term old ty
                -> term new ty)

namespace Single

  apply : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {ctxt   : List type}
       -> {typeA  : type}
       -> {typeB  : type}
       -> (this   : term      ctxt    typeB)
       -> (idx    : Contains (ctxt += typeB) typeA)
                 -> term      ctxt           typeA
  apply this Here = this
  apply this (There rest) = var rest

  export
  subst : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {ctxt          : List type}
       -> {typeA         : type}
       -> {typeB         : type}
       -> (this          : term  ctxt           typeB)
       -> (inThis        : term (ctxt += typeB) typeA)
                        -> term  ctxt           typeA
  subst {ctxt} {typeA} {typeB} this inThis
    = subst (apply this) inThis

namespace Double

  public export
  apply : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {ctxt          : List type}
       -> {typeA, typeB, typeC : type}
       -> (this    : term       ctxt                     typeA)
       -> (andThis : term       ctxt                     typeB)
       -> (idx     : Contains ((ctxt += typeA) += typeB) typeC)
                  -> term       ctxt                     typeC
  apply this andThis Here              = andThis
  apply this andThis (There Here)      = this
  apply this andThis (There (There x)) = var x

  public export
  subst : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {ctxt          : List type}
       -> {typeA, typeB, typeC : type}
       -> (this    : term  ctxt                     typeA)
       -> (andThis : term  ctxt                     typeB)
       -> (inThis  : term ((ctxt += typeA) += typeB) typeC)
                  -> term   ctxt                     typeC
  subst {ctxt} {typeA} {typeB} {typeC} this andThis inThis
    = General.subst (apply this andThis) inThis

-- [ EOF ]
