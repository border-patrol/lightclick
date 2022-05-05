||| Introduce fresh names for let bound things.
|||
||| Module    : FreshBinders.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.IR.Channel.Normalise.FreshBinders

import Data.List
import Data.Vect

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Core

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

import LightClick.IR.Channel.Normalise.Error
import LightClick.IR.Channel.Normalise.LetFloat

%default total

||| Introduce binders for module/gate instanstiation.
createModuleBinders : (state   : List String)
                   -> (counter : Nat)
                   -> (expr    : ChannelIR type)
                              -> ChannelIR type
createModuleBinders state counter (CLet bind this inThis)
  = CLet bind this $ createModuleBinders (bind::state) counter inThis

createModuleBinders state counter (CSeq (CModuleInst mname xs) y)
  = CLet ("lightclick_module_" <+> show counter)
         (CModuleInst mname xs)
         (createModuleBinders state (S counter) y)

createModuleBinders state counter (CSeq (CNot o i) y)
  = CLet ("lightclick_module_" <+> show counter)
         (CNot o i)
         (createModuleBinders state (S counter) y)

createModuleBinders state counter (CSeq (CGate ty o ins) y)
  = CLet ("lightclick_module_" <+> show counter)
         (CGate ty o ins)
         (createModuleBinders state (S counter) y)


createModuleBinders state counter (CSeq x y)
  = CSeq (createModuleBinders state counter x) y

createModuleBinders state counter expr
  = expr

||| Find all unbound constructs and bind them to fresh names.
export
covering -- from Let float.
freshBinders : (expr : ChannelIR type)
                    -> LightClick (ChannelIR type)
freshBinders expr
  = LetFloat.run (createModuleBinders Nil Z expr)


-- [ EOF ]
