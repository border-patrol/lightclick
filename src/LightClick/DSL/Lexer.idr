module LightClick.DSL.Lexer

import Text.Lexer

import Toolkit.Text.Lexer.Run

%default total


symbols : List String
symbols = ["->", "-", "[", "]", ";", "{", "}", ":", ",", "=", "?", "(", ")", ".", "#", "!", "&", "|", "+"]

keywords : List String
keywords = [ "input", "output", "inout"
           , "high", "low", "rising", "falling", "insensitive"
           , "control", "clock", "data", "address", "reset", "info", "interrupt", "general"
           , "types", "modules", "connections", "module"
           , "logic", "typedef", "struct", "union", "lightclick", "model", "verilog"
           ]

public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace LightClick
  public export
  data Token = ID String
               | Keyword String
               | LineComment String
               | BlockComment String
               | Documentation String
               | LitNat Nat
               | LitStr String
               | Symbol String
               | WS String
               | NotRecognised String
               | EndInput

  export
  Eq Token where
    (==) (ID x) (ID y) = x == y
    (==) (LineComment x) (LineComment y) = x == y
    (==) (BlockComment x) (BlockComment y) = x == y
    (==) (Keyword x) (Keyword y) = x == y
    (==) (LitNat x) (LitNat y) = x == y
    (==) (LitStr x) (LitStr y) = x == y
    (==) (Symbol x) (Symbol y) = x == y
    (==) (WS x) (WS y) = x == y
    (==) (NotRecognised x) (NotRecognised y) = x == y
    (==) EndInput EndInput = True
    (==) _ _ = False


  showToken : Show a => String -> a -> String
  showToken n a = "(" <+> n <+> " " <+> show a <+> ")"

  export
  Show Token where
    show (ID id)             = showToken "ID" id
    show (Keyword str)       = showToken "Keyword" str
    show (LineComment str)   = showToken "LineComment" str
    show (BlockComment str)  = showToken "BlockComment" str
    show (Documentation str) = showToken "Documentation" str

    show (LitNat n) = showToken "Nat" n
    show (LitStr s) = showToken "Str" s

    show (Symbol s) = showToken "Symbol" s
    show (WS ws) = "WS"
    show (NotRecognised s) = showToken "Urgh" s
    show EndInput          = "EndInput"

  identifier : Lexer
  identifier = pred startIdent <+> many (pred validIdent)
    where
      startIdent : Char -> Bool
      startIdent x = isAlpha x

      validIdent : Char -> Bool
      validIdent '_' = True
      validIdent x = isAlphaNum x



  export
  tokenMap : TokenMap LightClick.Token
  tokenMap = with List
    [
      (space, WS)
    , (lineComment (exact "//"), LineComment)
    , (blockComment (exact "/*") (exact "*/"), BlockComment)
    , (lineComment (exact "\\\\"), Documentation)
    , (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
    , (stringLit, LitStr)
    ]
    ++
       map (\x => (exact x, Symbol)) symbols
    ++
    [
      (identifier, (\x => if elem x keywords then Keyword x else ID x))
    , (any, NotRecognised)
    ]

keep : WithBounds LightClick.Token -> Bool
keep (MkBounded t _ _)
  = case t of
      BlockComment _ => False
      LineComment  _ => False
      WS           _ => False
      _              => True

export
LightClickLexer : Lexer Token
LightClickLexer = MkLexer LightClick.tokenMap (keep) EndInput

export
lexClickStr : String -> Either LexError (List (WithBounds Token))
lexClickStr = lexString LightClickLexer

export
lexClickFile : String -> IO $ Either LexFail (List (WithBounds Token))
lexClickFile = lexFile LightClickLexer
