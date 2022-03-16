module Toolkit.Options.ArgParse.Parser.API

import Data.List
import Data.String

import Text.Token
import Text.Lexer
import Text.Parser

import Toolkit.Options.ArgParse.Lexer
import public Toolkit.Text.Parser.Support


%default total

-- Some basic parsers used by all the intermediate forms

export
shortFlag : Rule Token String
shortFlag
    = terminal "Expected Short Flag"
               (\x => case tok x of
                           SFlag f => Just (substr 1 (length f) f)
                           _     => Nothing)

export
longFlag : Rule Token String
longFlag
    = terminal "Expected long flag"
               (\x => case tok x of
                           LFlag f => Just (substr 2 (length f) f)
                           _       => Nothing)

export
arg : Rule Token String
arg = terminal "Expected arg."
  (\x => case tok x of
           Arg s => Just (trim s)
           _     => Nothing)

export
equals : Rule Token ()
equals = terminal "Expected equals"
  (\x => case tok x of
           Equals _ => Just ()
           _        => Nothing)

export
quoted : Rule Token String
quoted = terminal "Expected quoted input"
    (\x => case tok x of
             Quoted s => Just $ rmQuotes s
             _        => Nothing)
  where
    rmQuotes : String -> String
    rmQuotes xs = pack $ filter (not . (==) '"') (unpack xs)

-- --------------------------------------------------------------------- [ EOF ]
