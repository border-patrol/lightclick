module Commons.Data.Location

%default total

public export
record Location where
  constructor MkLoc
  source : Maybe String
  line   : Nat
  col    : Nat

public export
record FileContext where
  constructor MkFC
  source : Maybe String
  start  : Location
  end    : Location

export
newFC : Maybe String -> Location -> Location -> FileContext
newFC n s e = MkFC n (record {source = n} s) (record {source = n} e)

namespace FromCoords
  export
  newLoc : Maybe String -> (Nat, Nat) -> Location
  newLoc n (l,c) = MkLoc n l c

  export
  newFC : Maybe String -> (Nat, Nat) -> (Nat, Nat) -> FileContext
  newFC n s e = newFC n (newLoc n s) (newLoc n e)

namespace Anon

  export
  newLoc : (Nat, Nat) -> Location
  newLoc (l,c) = MkLoc Nothing l c

  export
  newFC : Location -> Location -> FileContext
  newFC s e = newFC Nothing s e

export
emptyFC : FileContext
emptyFC = newFC Nothing (0,0) (0,0)

export
Show Location where
  show (MkLoc Nothing  l c) = with List concat [show l, ":", show c]
  show (MkLoc (Just n) l c) = with List concat [n, ":", show l, ":", show c]

export
Show FileContext where
  show (MkFC Nothing (MkLoc _ l scol) (MkLoc _ _ ecol)) = with List concat ["global:", show l, ":", show scol, "-", show ecol, ":"]
  show (MkFC (Just x) (MkLoc _ l scol) (MkLoc _ _ ecol)) = with List concat [x, ":", show l, ":", show scol, "-", show ecol, ":"]
