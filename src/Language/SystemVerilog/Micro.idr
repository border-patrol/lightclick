||| An AST for represening a subset of systemverilog.
|||
||| We assume that modules cannot be nested.
module Language.SystemVerilog.Micro

import Data.Vect

import Data.DList
import Data.DVect

import Data.Vect.Extra

import public Text.PrettyPrint.Prettyprinter

import public Language.SystemVerilog.MetaTypes
import public Language.SystemVerilog.Direction

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

    MDecl : (ports : DList String (\s => Expr lctxt gctxt (PORT s)) names)
         -> Expr lctxt gctxt (MODULE names)

    -- Ctors
    NewChan : Expr ctxt gctxt CHAN
    NewModule : List (Pair String (Expr ctxt gctxt CHAN))
             -> Expr ctxt gctxt (MINST names)

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


semiBrace : Vect n (Doc ())
         -> Doc ()
semiBrace xs
    = group (encloseSep
              (flatAlt (pretty "{") (pretty "{"))
              (flatAlt (pretty "}") (pretty "}"))
              (pretty "; ")
              (toList xs)
              )

mutual

  covering
  prettyDecls' : (decls : Decls gtypes) -> List (Doc ())
  prettyDecls' Empty = Nil
  prettyDecls' (DeclAdd this beThis IsDeclM rest )
    = prettyDecls' rest ++ [pretty "module" <++> pretty this <++> prettyExpr beThis <++> line]
  prettyDecls' (DeclAdd this beThis IsDeclD rest )
    = prettyDecls' rest ++ [pretty "typedef" <++> prettyExpr beThis <++> (pretty this <+> semi) <++> line]

  covering
  prettyDecls : (decls : Decls gtypes) -> Doc ()
  prettyDecls = (vsep . prettyDecls')

  covering
  prettyExpr : Expr lctxt gctxt type -> Doc ()

  prettyExpr End = emptyDoc
  prettyExpr TYPE = emptyDoc
  prettyExpr (Local label x) = pretty label
  prettyExpr (Global label x)   = pretty label

  prettyExpr (Let this beThis withType prf inThis) =
    vcat [ hsep [ prettyExpr withType
                , hcat [pretty this, prettyExpr beThis, semi]
                ]
         , prettyExpr inThis
         ]

  prettyExpr (Seq x y) =
    vcat [ prettyExpr x
         , prettyExpr y]

  prettyExpr DataLogic = pretty "logic"

  prettyExpr (DataArray type size) =
          prettyExpr type
      <+> brackets (pretty size)

  prettyExpr (DataStruct xs) =
    let xs' = map (\(l,d) => hsep [prettyExpr d, pretty l]) xs
     in pretty "struct" <++> semiBrace xs'

  prettyExpr (DataUnion xs) =
    let xs' = map (\(l,d) => hsep [prettyExpr d, pretty l]) xs in
      pretty "union" <++> semiBrace  xs'

  prettyExpr (Port label dir type) =
    hsep [ prettyDir dir
         , prettyExpr type
         , pretty label
         ]
  prettyExpr (MDecl x) =
    vcat [ (tupled $ mapToList prettyExpr x) <+> semi
         , pretty "endmodule"
         ]

  prettyExpr NewChan = emptyDoc
  prettyExpr (NewModule xs) =
    let params = map (\(l,c) => pretty "." <+> pretty l <+> parens (prettyExpr c)) xs in tupled (params)

export
covering
prettySpec : Spec -> Doc ()
prettySpec (MkSpec rest x) =
  vcat [ prettyDecls rest
       , pretty "begin Top ();"
       , indent 4 (prettyExpr x)
       , pretty "endmodule"]

-- --------------------------------------------------------------------- [ EOF ]
