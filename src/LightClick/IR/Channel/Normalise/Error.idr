module LightClick.IR.Channel.Normalise.Error

import Data.String

%default total

namespace Normalise
  public export
  data Error = ModuleInlined | NoModuleInstances

  export
  Show Error where
    show ModuleInlined     = "Normalisation Error: Module Inlined"
    show NoModuleInstances = "Normalisation Error: No Module instances found"

public export
Normalise : Type -> Type
Normalise = Either Error


-- [ EOF ]
