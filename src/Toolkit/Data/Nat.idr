module Toolkit.Data.Nat

%default total

public export
toNat : Int -> Nat
toNat = (integerToNat . cast)
