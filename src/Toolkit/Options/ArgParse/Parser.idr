-- -------------------------------------------------------------- [ Parser.idr ]
-- Description : A simple parser for command options.
-- Copyright   : (c) Jan de Muijnck-Hughes
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Toolkit.Options.ArgParse.Parser

import Text.Lexer
import Text.Parser

import Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Run

import Toolkit.Options.ArgParse.Lexer
import Toolkit.Options.ArgParse.Parser.API
import Toolkit.Options.ArgParse.Model

-- ----------------------------------------------------------------- [ Parsers ]

flagLong : Rule Token Arg
flagLong = do
  l <- longFlag
  pure $ Flag l

flagShort : Rule Token Arg
flagShort = do
   s <- shortFlag
   pure $ Flag s

kvLong : Rule Token Arg
kvLong = do
    key <- longFlag
    equals
    value <- (arg <|> quoted)
    pure $ KeyValue key value

kvShort : Rule Token Arg
kvShort = do
    k <- shortFlag
    v <- (arg <|> quoted)
    pure $ KeyValue k v

options : Rule Token Arg
options = kvShort <|> kvLong <|> flagShort <|> flagLong <|> (do fs <- arg; pure $ File fs)

args : RuleEmpty Token $ List Arg
args = do
    os <- many options
    pure $ os

export
parseArgsStr : (str  : String)
            -> Either (Run.ParseError Token) (List Arg)
parseArgsStr str = parseString ArgParseLexer args str

export
parseArgsFile :(fname : String)
            -> IO (Either (Run.ParseError Token) (List Arg))
parseArgsFile fn = parseFile ArgParseLexer args fn

-- --------------------------------------------------------------------- [ EOF ]
