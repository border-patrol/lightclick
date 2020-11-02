module Language.SystemVerilog.Micro.Pretty

import Data.Vect

import Data.DList
import Data.DVect

import Data.Vect.Extra

import public Text.PrettyPrint.Prettyprinter

import Language.SystemVerilog.Micro

%default total

krStyle : (l,r  : Doc ())
       -> (body : List (Doc ()))
               -> Doc ()
krStyle l r body = vsep [l, indent 2 (align $ vcat body), r]

krStyleParams : (l,r  : Doc ())
             -> (sep  : Doc ())
             -> (body : List (Doc ()))
                     -> Doc ()
krStyleParams l r sep body = vsep [l, indent 2 (align $ vcat (punctuate sep body)), r]


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
    vsep [ hsep [ prettyExpr withType
                , hcat [pretty this, prettyExpr beThis, semi]
                ]
         , prettyExpr inThis
         ]

  prettyExpr (Seq x y) =
    vcat [ prettyExpr x
         , prettyExpr y]

  prettyExpr DataLogic = pretty "logic"

  prettyExpr (DataArray type Z) = prettyExpr type
  prettyExpr (DataArray type (S size)) =
          prettyExpr type
      <+> brackets (pretty size <+> colon <+> pretty "0")

  prettyExpr (DataStruct xs) =
    let xs' = map (\(l,d) => hsep [prettyExpr d, pretty l <+> semi]) xs
     in pretty "struct packed" <+> hardline <+> krStyle lbrace rbrace (toList xs')

  prettyExpr (DataUnion xs) =
    let xs' = map (\(l,d) => hsep [prettyExpr d, pretty l <+> semi]) xs in
      pretty "union packed" <+> hardline <+> krStyle lbrace rbrace (toList xs')

  prettyExpr (Port label dir type) =
    hsep [ prettyDir dir
         , prettyExpr type
         , pretty label
         ]
  prettyExpr (MDecl x) =
    vcat [ softline
         , krStyleParams lparen rparen comma (mapToList prettyExpr x) <+> semi
         , pretty "// TO ADD"
         , pretty "endmodule;"
         ]

  prettyExpr NewChan = emptyDoc
  prettyExpr (NewModule xs) =
    let params = map (\(l,c) => dot <+> pretty l <+> parens (prettyExpr c)) xs
    in let ps' = indent 2 (krStyleParams lparen rparen comma params)
    in hardline <++> ps'

export
covering
prettySpec : Spec -> Doc ()
prettySpec (MkSpec rest x) =
  vcat [ prettyDecls rest
       , pretty "module Top ();"
       , indent 2 (prettyExpr x)
       , pretty "endmodule;"]

-- [ EOF ]
