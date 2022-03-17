||| An AST for represening a subset of systemverilog.
|||
||| We assume that modules cannot be nested.
module Language.SystemVerilog.Micro

import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.Vect.Extra

import public Language.SystemVerilog.MetaTypes
import public Language.SystemVerilog.Direction
import public Language.SystemVerilog.Gates

%default total

public export
data Expr : (lctxt : Context)
         -> (gctxt : Context)
         -> (type : Ty)
         -> Type
  where
    End : Expr ctxt gctxt UNIT

    Local : (  label : String)
         -> (  idx   : Index lctxt (label, type))
                    -> Expr lctxt gctxt type

    Global : {ty : Ty}
          -> (label : String)
          -> (idx   : Index gctxt (label, ty))
          -> Expr lctxt gctxt ty

    Let : (  this     : String)
       -> (  beThis   : Expr ctxt gctxt typeE)
       -> (  withType : Expr ctxt gctxt type)
       -> (  prf      : ValidLet typeE type)
       -> (  inThis   : Expr ((this,typeE)::ctxt) gctxt typeB)
       -> Expr ctxt gctxt typeB

    Seq : {typeA,typeB : Ty}
       -> (this : Expr ctxt gctxt typeA)
       -> (that : Expr ctxt gctxt typeB)
       -> Expr ctxt gctxt typeB

    TYPE : Expr lctxt gctxt TYPE

    GATE : Expr lctxt gctxt GATE

    -- Decls
    DataLogic : Expr lctxt gctxt DATA

    DataArray : (type : Expr lctxt gctxt DATA)
             -> (size : Nat)
             -> Expr lctxt gctxt DATA

    DataStruct : (xs : Vect (S n) (Pair String (Expr lctxt gctxt DATA)))
              -> Expr lctxt gctxt DATA

    DataUnion : (xs : Vect (S n) (Pair String (Expr lctxt gctxt DATA)))
             -> Expr lctxt gctxt DATA

    Port : (label : String)
        -> (dir   : Direction)
        -> (type  : Expr lctxt gctxt DATA)
        -> Expr lctxt gctxt (PORT label)

    MDecl : (ports : DList String (Expr lctxt gctxt . PORT) names)
         -> Expr lctxt gctxt (MODULE names)

    -- Ctors
    NewChan : Expr ctxt gctxt CHAN
    NoOp : Expr ctxt gctxt CHAN
    NewModule : DList String (\s => Pair (Label s) (Expr ctxt gctxt CHAN)) names
             -> Expr ctxt gctxt (MINST names)

    -- Gates
    Not : (out : Expr ctxt gctxt CHAN)
       -> (ins : Expr ctxt gctxt CHAN)
       -> Expr ctxt gctxt GINST

    Gate : {n : Nat}
        -> (type : TyGateComb)
        -> (out  : Expr ctxt gctxt CHAN)
        -> (ins  : Vect (S (S n)) (Expr ctxt gctxt CHAN))
                -> Expr ctxt gctxt GINST


public export
data Decls : (global : Context) -> Type where
  Empty   : Decls Nil
  DeclAdd : (binder : String)
         -> (expr   : Expr Nil global type)
         -> (prf    : ValidDecl type TYPE)
         -> (rest   : Decls global)
         -> Decls ((MkPair binder type) :: global)

public export
record Spec where
  constructor MkSpec
  decls : Decls gtypes
  expr  : Expr Nil gtypes UNIT


export
getMetaType : {type : _} -> Expr local global type -> Ty
getMetaType {type} _ = type



-- --------------------------------------------------------------------- [ EOF ]
