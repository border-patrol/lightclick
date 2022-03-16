-- --------------------------------------------------------------- [ Error.idr ]
-- Module    : Error.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Toolkit.Options.ArgParse.Error

import Data.String

import System.File

import Toolkit.Data.Location

import Toolkit.Options.ArgParse.Model
import Toolkit.Options.ArgParse.Lexer
import Toolkit.Options.ArgParse.Parser

%default total

public export
data ArgParseError : Type where
  InvalidOption   : Arg -> ArgParseError
  MalformedOption : ParseError Token -> ArgParseError

export
(Show Arg) => Show ArgParseError where
  show (InvalidOption o) = "Invalid Option " ++ show o
  show (MalformedOption (PError (MkParseFail error location rest))) =
    unlines [show location, error]
  show (MalformedOption (LError (MkLexFail l i)))  = unwords [show l, ":\n" <+> i]
  show (MalformedOption (FError x))  = unlines ["File Error:", show x]


-- --------------------------------------------------------------------- [ EOF ]
