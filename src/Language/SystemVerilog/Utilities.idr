module Language.SystemVerilog.Utilities

import Data.List

%default total

export
newName : (xs  : List String)
       -> (prf : NonEmpty xs)
              => String
newName (x::xs) {prf=IsNonEmpty} = concat (intersperse "_" (x::xs))
