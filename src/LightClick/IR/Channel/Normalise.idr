module LightClick.IR.Channel.Normalise

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Types
import LightClick.Terms

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

import public LightClick.IR.Channel.Normalise.Error
import LightClick.IR.Channel.Normalise.LetFloat
import LightClick.IR.Channel.Normalise.Merge
import LightClick.IR.Channel.Normalise.FreshBinders

%default total

export
covering -- comes from Merge runMerge not being total.
normalise : ChannelIR UNIT -> Either Normalise.Error (ChannelIR UNIT)
normalise expr =
  do e'   <- runLetFloat expr
     em'  <- runMerge e'
     emb' <- freshBinders em'
     pure emb'

-- --------------------------------------------------------------------- [ EOF ]
