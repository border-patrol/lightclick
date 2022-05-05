||| Translation errors when converting to MicroSV.
|||
||| Module    : MicroSV/Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| We do not expect these to occur, as the original input terms are
||| well-scoped and well-typed, however the translation code is not as
||| robust: mistakes may happen during development.
|||
module LightClick.IR.Channel.MicroSV.Error

import Data.String

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
  show (IdentifierNotFound x)
    = unwords ["Identifier Not Found:", show x]

  show (UnexpectedType x)
    = unwords ["Unexpected Type:", show x]

  show MalformedExpr
    = "Malformed Expression"

  show (General err)
    = unwords ["Generic Error:", err]

  show (Nested desc err)
    = desc ++ "\n" ++ show err


-- [ EOF ]
