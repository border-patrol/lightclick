||| Normalise the Channelised terms.
|||
||| Module    : Normalise.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| This will:
|||
||| 1. Float lets to the top.
||| 2. Merge all module instantiations.
||| 3. Generate fresh binders for bindable terms.
|||
module LightClick.IR.Channel.Normalise

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Core

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

import LightClick.IR.Channel.Normalise.LetFloat
import LightClick.IR.Channel.Normalise.Merge
import LightClick.IR.Channel.Normalise.FreshBinders

%default total

||| Normalise channelised IR.
|||
||| This will:
|||
||| 1. Float lets to the top.
||| 2. Merge all module instantiations.
||| 3. Generate fresh binders for bindable terms.
export
covering -- comes from Merge runMerge not being total.
normalise : ChannelIR UNIT
         -> LightClick (ChannelIR UNIT)
normalise expr =
  do e'   <- LetFloat.run expr
     em'  <- Merge.run e'
     emb' <- freshBinders em'
     pure emb'

-- --------------------------------------------------------------------- [ EOF ]
