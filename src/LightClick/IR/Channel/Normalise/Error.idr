||| The Errors that occur during normalisation.
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.IR.Channel.Normalise.Error

import Data.String

%default total

namespace Normalise
  public export
  data Error = ModuleInlined | NoModuleInstances

  export
  Show Error where
    show ModuleInlined
      = "Normalisation Error: Module Inlined"

    show NoModuleInstances
      = "Normalisation Error: No Module instances found"

-- [ EOF ]
