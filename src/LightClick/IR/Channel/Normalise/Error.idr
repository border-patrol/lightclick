module LightClick.IR.Channel.Normalise.Error

import Data.Strings

%default total

public export
data MError = ModuleInlined | NoModuleInstances

public export
data NError = MergeError MError

export
Show MError where
  show ModuleInlined = "Module Inlined"
  show NoModuleInstances = "No Module instances found"

export
Show NError where
  show (MergeError err) = unlines ["Normalisation Error", show err]
