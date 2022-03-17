module Toolkit.Data.DVect.View.Shape

import Toolkit.Data.DVect

%default total

public export
data Shape : (xs : DVect kind type n ns)
          -> (ys : DVect kind type m ms)
                -> Type
  where
    Empty : Shape     Nil     Nil
    LH    : Shape (x::xs)     Nil
    RH    : Shape     Nil (y::ys)
    Both  : Shape (x::xs) (y::ys)

export
shape : (xs : DVect kind type n ns)
     -> (ys : DVect kind type m ms)
           -> Shape xs ys
shape [] []
  = Empty

shape [] (y :: ys)
  = RH

shape (x :: xs) []
  = LH

shape (x :: xs) (y :: ys)
  = Both


-- [ EOF ]
