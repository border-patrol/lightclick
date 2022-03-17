module Language.SystemVerilog.Direction

%default total

public export
data Direction = IN | INOUT | OUT

export
Show Direction where
  show IN    = "input"
  show OUT   = "output"
  show INOUT = "inout"


-- --------------------------------------------------------------------- [ EOF ]
