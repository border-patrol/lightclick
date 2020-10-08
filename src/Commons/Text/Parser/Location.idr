module Commons.Text.Parser.Location

import Text.Lexer
import Text.Parser

import Commons.Data.Nat
import Commons.Data.Location
import Commons.Text.Parser.Support

%default total

export
column : RuleEmpty tok Nat
column = do
  tok <- peek
  pure ((toNat . col) tok)

export
location : RuleEmpty tok Location
location = do
  tok <- peek
  pure (MkLoc Nothing ((toNat . line) tok) ((toNat . col) tok))


namespace WithFileName
  export
  location : String -> RuleEmpty tok Location
  location fname = do
    l <- location
    pure (record { source = Just fname} l)
