module Language.SystemVerilog.Micro.Pretty

import Data.Vect

import public Text.PrettyPrint.Prettyprinter

import Toolkit.Data.DList
import Toolkit.Data.DVect

import Toolkit.Data.Vect.Extra

import Language.SystemVerilog.Gates

import Language.SystemVerilog.Micro

%default covering

krStyle : (l,r  : Doc ())
       -> (body : List (Doc ()))
               -> Doc ()
krStyle l r body = vsep [l, indent 2 (align $ vcat body), r]

krStyleParams : (l,r  : Doc ())
             -> (sep  : Doc ())
             -> (body : List (Doc ()))
                     -> Doc ()
krStyleParams l r sep body = vsep [l, indent 2 (align $ vcat (punctuate sep body)), r]

prettyGate : TyGateComb -> Doc ()
prettyGate = (pretty . show)

prettyDir : Direction -> Doc ()
prettyDir = (pretty . show)

prettyExpr : Expr lctxt gctxt type -> Doc ()

prettyDecls' : (decls : Decls gs) -> List (Doc ())

prettyFields : Vect n (Pair String (Expr l g DATA))
            -> Doc ()
prettyFields
  = (krStyle lbrace rbrace . toList . map (\(l,d) => hsep [prettyExpr d, pretty l <+> semi]))

prettyDecls : (decls : Decls gs) -> Doc ()
prettyDecls = (vsep . prettyDecls')


prettyDecls' Empty
  = Nil

prettyDecls' (DeclAdd this beThis IsDeclM rest)
  = prettyDecls' rest ++ [pretty "module" <++> pretty this <++> prettyExpr beThis <++> line]

prettyDecls' (DeclAdd this beThis IsDeclD rest)
  = prettyDecls' rest ++ [pretty "typedef" <++> prettyExpr beThis <++> (pretty this <+> semi) <++> line]

prettyExpr End
  = emptyDoc
prettyExpr TYPE
  = emptyDoc
prettyExpr GATE
  = emptyDoc

prettyExpr (Local label _)
   = pretty label

prettyExpr (Global label _)
  = pretty label

prettyExpr (Let this beThis withType IsLetCD inThis)
  = vsep [ hsep [ pretty "wire"
                , prettyExpr withType
                , hcat [pretty this, prettyExpr beThis, semi]
                ]
         , prettyExpr inThis
         ]

prettyExpr (Let this (Not o i) withType IsLetGG inThis)
  = vsep [ hsep [ pretty "not"
                , hcat [pretty this, prettyExpr (Not o i), semi]
                ]
         , prettyExpr inThis
         ]

prettyExpr (Let this (Gate ty o ins) withType IsLetGG inThis)
  = vsep [ hsep [ prettyGate ty
                , hcat [pretty this, prettyExpr (Gate ty o ins), semi]
                ]
         , prettyExpr inThis
         ]

prettyExpr (Let this beThis withType prf inThis)
  = vsep [ hsep [ prettyExpr withType
                , hcat [pretty this, prettyExpr beThis, semi]
                ]
         , prettyExpr inThis
         ]

prettyExpr (Seq this that)
  = vcat [ prettyExpr this
         , prettyExpr that]

prettyExpr DataLogic
  = pretty "logic"

prettyExpr (DataArray type Z)
  = prettyExpr type

prettyExpr (DataArray type (S size))
  = prettyExpr type <+> brackets (pretty size <+> colon <+> pretty "0")

prettyExpr (DataStruct xs)
  = pretty "struct packed" <+> hardline <+> (prettyFields xs)

prettyExpr (DataUnion xs)
  = pretty "union packed" <+> hardline <+> (prettyFields xs)

prettyExpr (Port label dir type)
  = hsep [ prettyDir dir
         , prettyExpr type
         , pretty label
         ]

prettyExpr (MDecl ports)
  = vcat [ softline
         , krStyleParams lparen rparen comma (mapToList prettyExpr ports) <+> semi
         , pretty "// TO ADD"
         , pretty "endmodule;"
         ]

prettyExpr NoOp
  = emptyDoc

prettyExpr NewChan
  = emptyDoc

prettyExpr (NewModule xs)
  = let params = assert_total $ mapToList (\(L l,c) => dot <+> pretty l <+> parens (prettyExpr c)) xs
    in let ps' = indent 2 (krStyleParams lparen rparen comma params)
    in hardline <++> ps'

prettyExpr (Not out ins)
  = krStyle lparen rparen (punctuate comma $ [prettyExpr out, prettyExpr ins])

prettyExpr (Gate x out ins)
  = let ins' = map prettyExpr ins
    in krStyle lparen rparen (punctuate comma $ prettyExpr out :: (toList ins'))

export
prettySpec : Spec -> Doc ()
prettySpec (MkSpec rest x) =
  vcat [ prettyDecls rest
       , pretty "module Top ();"
       , indent 2 (prettyExpr x)
       , pretty "endmodule;"]

-- [ EOF ]
