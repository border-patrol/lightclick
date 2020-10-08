module Language.SystemVerilog.Direction

import Text.PrettyPrint.Prettyprinter

%default total

public export
data Direction = IN | INOUT | OUT

export
prettyDir : Direction
         -> Doc ()
prettyDir IN    = pretty "input"
prettyDir OUT   = pretty "output"
prettyDir INOUT = pretty "inout"

-- --------------------------------------------------------------------- [ EOF ]
