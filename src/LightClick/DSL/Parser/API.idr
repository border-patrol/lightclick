module LightClick.DSL.Parser.API

import        Data.Vect
import        Data.List
import        Data.List1
import        Data.String
import        Data.Maybe

import public Text.Lexer
import public Text.Parser

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import        Language.SystemVerilog.Gates

import        LightClick.Types.Direction
import        LightClick.Types.Sensitivity
import        LightClick.Types.WireType

import        LightClick.DSL.AST

import public LightClick.DSL.Lexer

namespace LightClick
  public export
  Rule : Type -> Type
  Rule = Rule () Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty () Token

  export
  eoi : RuleEmpty ()
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

export
symbol : String -> Rule ()
symbol str
  = terminal ("Expected Symbol '" ++ str ++ "'")
             (\x => case x of
                           Symbol s => if s == str then Just ()
                                                   else Nothing
                           _ => Nothing)

export
keyword : String -> Rule ()
keyword str
  = terminal ("Expected Keyword '" ++ str ++ "'")
               (\x => case x of
                           Keyword s => if s == str then Just ()
                                                    else Nothing
                           _ => Nothing)

export
natLit : Rule Nat
natLit = terminal "Expected nat literal"
             (\x => case x of
                         LitNat i => Just i
                         _ => Nothing)

export
strLit : Rule String
strLit = terminal "Expected string literal"
             (\x => case x of
                         LitStr s => Just s
                         _ => Nothing)

export
identifier : Rule String
identifier
  = terminal "Expected Identifier"
             (\x => case x of
                                ID str => Just str
                                _ => Nothing)

export
doc : Rule (List1 String)
doc = some docString
  where
    docString : Rule String
    docString = terminal "Documentation String"
                         (\x => case x of
                                     Documentation doc => Just doc
                                     _ => Nothing)

export
name : Rule String
name = identifier

export
arrow : Rule ()
arrow = symbol "->"

export
braces : Rule a
      -> Rule a
braces p
  = do symbol "["
       a <- p
       symbol "]"
       pure a

export
brackets : (Rule a)
        -> Rule a
brackets = between (symbol "{") (symbol "}")

export
parens : (Rule a)
      -> Rule a
parens = between (symbol "(") (symbol ")")

export
sepBy1V : (sep : Rule b)
       -> (p : Rule a)
       -> Rule (n ** Vect (S n) a)
sepBy1V sep p = do {x <- p; xs <- many (sep *> p); pure (_ ** fromList $ x::xs)}

export
sepBy2V : (sep : Rule ())
       -> (p : Rule a)
       -> Rule (n ** Vect (S (S n)) a)
sepBy2V sep p
  = do x <- p
       sep
       y <- p
       rest <- many (sep *> p)
       pure (_ ** fromList $ x::y::rest)

export
commaSepBy1V : (p : Rule a) -> Rule (n ** Vect (S n) a)
commaSepBy1V = sepBy1V (symbol ",")

export
commaSepBy2V : (p : Rule a) -> Rule (n ** Vect (S (S n)) a)
commaSepBy2V = sepBy2V (symbol ",")


-- [ EOF ]
