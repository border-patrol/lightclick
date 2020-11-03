module LightClick.IR.Channel.Normalise.FreshBinders

import Data.List
import Data.Vect

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Types
import LightClick.Terms
import LightClick.Error

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

import LightClick.IR.Channel.Normalise.LetFloat

%default total

createModuleBinders : (state : List String)
                   -> (counter : Nat)
                   -> (expr  : ChannelIR type)
                   -> ChannelIR type
createModuleBinders state counter (CLet bind this inThis)
  = CLet bind this $ createModuleBinders (bind::state) counter inThis

createModuleBinders state counter (CSeq (CModuleInst mname xs) y)
  = CLet ("lightclick_module_" <+> show counter)
         (CModuleInst mname xs)
         (createModuleBinders state (S counter) y)

createModuleBinders state counter (CSeq x y)
  = CSeq (createModuleBinders state counter x) y

createModuleBinders state counter expr = expr

export
covering
freshBinders : (expr : ChannelIR type)
                    -> Either LightClick.Error
                              (ChannelIR type)
freshBinders expr
  = runLetFloat (createModuleBinders Nil Z expr)


-- [ EOF ]
