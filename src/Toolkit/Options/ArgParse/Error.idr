-- --------------------------------------------------------------- [ Error.idr ]
-- Module    : Error.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Toolkit.Options.ArgParse.Error

import Data.List1
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
Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
Show a => Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]

export
(Show Arg) => Show ArgParseError where
  show (InvalidOption o)
    = "Invalid Option " ++ show o
  show (MalformedOption err)
    = show err


-- --------------------------------------------------------------------- [ EOF ]
