module Toolkit.Text.Parser.Run

import System.File

import Text.Parser
import Text.Lexer

import Toolkit.Data.Nat
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run

import Toolkit.Text.Parser.Support


%default total

public export
record ParseFailure a where
  constructor MkParseFail
  error : String
  location : Maybe Location
  rest : List a

public export
data ParseError a = PError (ParseFailure a)
                  | LError LexError
                  | FError FileError


export
convError : Core.ParseError (TokenData a)
         -> Maybe String
         -> Run.ParseError a
convError (Error msg Nil) _ = PError (MkParseFail msg Nothing Nil)
convError (Error msg (r::rs)) mn = PError $
    MkParseFail msg (Just $ MkLoc mn (toNat (TokenData.line r))
                                     (toNat (TokenData.col r)))
                    (map tok (r::rs))

export
parseString : {e     : _}
           -> (lexer : Lexer a)
           -> (rule  : Grammar (TokenData a) e ty)
           -> (str   : String)
                   -> (Either (Run.ParseError a) ty)
parseString lexer rule str =
  case lexString lexer str of
    Left err   => Left (LError err)
    Right toks =>
      case parse rule toks of
        Left err      => Left (convError err Nothing)
        Right (val,_) => Right val

export
covering
parseFile : {e     : _}
         -> (lexer : Lexer a)
         -> (rule  : Grammar (TokenData a) e ty)
         -> (fname : String)
         -> IO $ Either (Run.ParseError a) ty
parseFile lexer grammar fname =
  case !(lexFile lexer fname) of
    Left (LError err) => pure (Left (LError err))
    Left (LIOErr err) => pure (Left (FError err))
    Right toks =>
      case parse grammar toks of
        Left err      => pure (Left (convError err (Just fname)))
        Right (val,_) => pure (Right val)

-- --------------------------------------------------------------------- [ EOF ]
