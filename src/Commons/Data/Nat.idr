module Commons.Data.Nat

%default total

public export
toNat : Int -> Nat
toNat = (integerToNat . cast)
