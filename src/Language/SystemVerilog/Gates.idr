module Language.SystemVerilog.Gates


%default total

public export
data TyGateComb = AND | IOR | XOR

export
toString : TyGateComb -> String
toString AND = "and"
toString IOR = "ior"
toString XOR = "xor"
