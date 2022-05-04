module Toolkit.Data.Graph.EdgeBounded.Valid

import public Data.List.Quantifiers

import        Toolkit.Decidable.Informative

import        Toolkit.Data.Graph.EdgeBounded
import public Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All


%default total

public export
data ValidGraph : Graph type -> Type where
  IsValid : HasExactDegrees vs es
         -> ValidGraph (MkGraph vs es)

export
validGraph : {type : Type}
          -> (g    : Graph type)
                  -> DecInfo (HasExactDegree.Error type)
                             (ValidGraph g)
validGraph (MkGraph nodes edges) with (hasExactDegrees nodes edges)
  validGraph (MkGraph nodes edges) | (Yes prf)
    = Yes (IsValid prf)
  validGraph (MkGraph nodes edges) | (No msg contra)
    = No msg (\(IsValid prf) => contra prf)

-- [ EOF ]
