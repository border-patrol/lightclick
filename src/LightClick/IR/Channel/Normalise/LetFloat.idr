module LightClick.IR.Channel.Normalise.LetFloat

import Data.List
import Data.Vect
import Data.DList
import Data.DVect

import LightClick.Types
import LightClick.Terms
import LightClick.Error

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

%default total


isNF : ChannelIR type -> Bool

isNF (CSeq (CSeq this thenThis) andThis) = False

isNF (CSeq (CLet _ _ _) (CLet _ _ _)) = False

isNF (CSeq (CLet _ _ _) thenThis) = False

isNF (CSeq this (CLet _ _ _)) = False

isNF (CSeq this thenThis) = isNF this && isNF thenThis
isNF (CLet this beThis inThis) = isNF beThis && isNF inThis
isNF expr = True

letFloat : ChannelIR type -> ChannelIR type
letFloat (CSeq (CSeq this thenThis) rest) =
    CSeq (letFloat this)
         (CSeq (letFloat thenThis)
               (letFloat rest))

letFloat (CSeq (CLet outerName beOuterThis inOuterThis)
                  (CLet innerName beInnerThis inInnerThis)) =
    CLet outerName (letFloat beOuterThis)
         (CLet innerName (letFloat beInnerThis)
               (CSeq (letFloat inOuterThis)
                     (letFloat inInnerThis)))

letFloat (CSeq (CLet name beThis inThis)
                  thenDoThis) =
    CLet name (letFloat beThis)
         (CSeq (letFloat inThis)
               (letFloat thenDoThis))

letFloat (CSeq this
                  (CLet name beThis inThis)) =
    CLet name (letFloat beThis)
         (CSeq (letFloat this)
               (letFloat inThis))


letFloat (CLet x y z) = CLet x (letFloat y) (letFloat z)
letFloat (CSeq x y) = CSeq (letFloat x) (letFloat y)
letFloat expr = expr

export
covering -- due to totality checker not liking recursive calls.
runLetFloat : ChannelIR type -> Either LightClick.Error (ChannelIR type)
runLetFloat expr =
  if isNF expr
  then Right expr
  else runLetFloat (letFloat expr)


-- [ EOF ]
