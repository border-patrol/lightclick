module LightClick.IR.Channel.MicroSV.Error

import Data.Strings

import Language.SystemVerilog.MetaTypes

%default total

public export
data TError = IdentifierNotFound String
            | UnexpectedType Ty
            | MalformedExpr
            | General String
            | Nested String TError

export
Show TError where
  show (IdentifierNotFound x) = unwords ["Identifier Not Found:", show x]
  show (UnexpectedType x) = unwords ["Unexpected Type:", show x]
  show MalformedExpr = "Malformed Expression"
  show (General err) = unwords ["Generic Error:", err]
  show (Nested desc err) = desc ++ "\n" ++ show err
