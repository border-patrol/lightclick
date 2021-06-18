module LightClick.IR.Channel.Normalise.Merge

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Types
import LightClick.Terms

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric
import LightClick.IR.Channel.Normalise.Error

%default total

data State = Empty | RepeatedName | UniqueNames (List String) | InlineModule

||| If the name has been seen return nothing, otherwise extend the state.
updateState : State -> String -> State
updateState Empty y = UniqueNames [y]
updateState RepeatedName y = RepeatedName
updateState (UniqueNames xs) y with (isElem y xs)
  updateState (UniqueNames xs) y | (Yes prf) = RepeatedName
  updateState (UniqueNames xs) y | (No contra) = UniqueNames (y::xs)

updateState InlineModule y = InlineModule

||| A ChannelIR specification is in module normal form if each CModuleInst has a unique type.
|||
||| Returns nothing if a name is repeated, other wise a list of unique names.
isModuleNF : (state : State)
          -> (expr  : ChannelIR type)
                   -> State
isModuleNF state (CLet n beThis inThis)
  = isModuleNF (isModuleNF state beThis) inThis

isModuleNF state (CSeq this thenThis)
  = isModuleNF (isModuleNF state this) thenThis

isModuleNF state (CModuleInst (CRef mname MODULE) xs)
  = updateState state mname

isModuleNF state (CModuleInst mname xs)  = InlineModule
isModuleNF state expr = state


||| Remove all instances of CModuleInst and merge them together.
mergeModules : (state : List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN))))
            -> (expr  : ChannelIR type)
                     -> ChannelIR type
mergeModules state (CLet x y z)
  = CLet x (mergeModules state y) (mergeModules state z)
mergeModules state (CSeq (CModuleInst m@(CRef name MODULE) cs) y)
  = mergeModules ((name, (m,toList cs))::state) y

mergeModules state (CSeq x y) = CSeq x (mergeModules state y)

mergeModules state CEnd = rebuild CEnd (reduce Nil state)
  where
    rebuild : ChannelIR UNIT
           -> List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN)))
           -> ChannelIR UNIT
    rebuild u Nil     = u
    rebuild u ((_,(m,Nil))::xs) = (rebuild u xs) -- shouldn't happen
    rebuild u ((_,(m,c::cs))::xs) = CSeq (CModuleInst m (c::(fromList cs))) (rebuild u xs)

    action : String
          -> ChannelIR MODULE
          -> List (String, ChannelIR CHAN)
          -> List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN)))
          -> List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN)))
    action k inst cs Nil                          = [(k,(inst,cs))]
    action k inst cs ((name, (inst', cs')) :: rest) with (decEq k name)
      action k inst cs ((k, (inst', cs')) :: rest) | (Yes Refl)
        = (k, (inst', cs ++ cs')) :: rest
      action k inst cs ((name, (inst', cs')) :: rest) | (No contra)
        = (name, (inst', cs')) :: (action k inst cs rest)

    reduce : List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN))) -- turn into map
          -> List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN)))
          -> List (String, (ChannelIR MODULE, List (String, ChannelIR CHAN)))
    reduce new Nil = new
    reduce new ((k,(inst, cs))::xs) = reduce (action k inst cs new) xs

mergeModules state expr = expr

export
covering
runMerge : ChannelIR type -> Either Normalise.Error (ChannelIR type)
runMerge expr =
  case isModuleNF Empty expr of
    Empty => Left (NoModuleInstances)
    InlineModule => Left (ModuleInlined)
    RepeatedName => runMerge (mergeModules Nil expr)
    UniqueNames _ => Right expr


-- --------------------------------------------------------------------- [ EOF ]
