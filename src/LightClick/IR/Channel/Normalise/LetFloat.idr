||| Float lets to the top of the module description.
|||
||| Module    : LetFloat.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.IR.Channel.Normalise.LetFloat

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Core

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric

import LightClick.IR.Channel.Normalise.Error

%default total

||| Have we floated everything...
isNF : ChannelIR type
    -> Bool

isNF (CSeq (CSeq this thenThis) andThis)
  = False

isNF (CSeq (CLet _ _ _) (CLet _ _ _))
  = False

isNF (CSeq (CLet _ _ _) thenThis)
  = False

isNF (CSeq this (CLet _ _ _))
  = False

isNF (CSeq this thenThis)
  = isNF this && isNF thenThis

isNF (CLet this beThis inThis)
  = isNF beThis && isNF inThis

isNF expr
  = True

||| Float Let's to the top.
letFloat : ChannelIR type
        -> ChannelIR type

letFloat (CSeq (CSeq this thenThis) rest)
  = CSeq (letFloat this)
         (CSeq (letFloat thenThis)
               (letFloat rest))

letFloat (CSeq (CLet outerName beOuterThis inOuterThis)
                  (CLet innerName beInnerThis inInnerThis))

  = CLet outerName (letFloat beOuterThis)
         (CLet innerName (letFloat beInnerThis)
               (CSeq (letFloat inOuterThis)
                     (letFloat inInnerThis)))

letFloat (CSeq (CLet name beThis inThis)
                  thenDoThis)
  = CLet name (letFloat beThis)
         (CSeq (letFloat inThis)
               (letFloat thenDoThis))

letFloat (CSeq this
                  (CLet name beThis inThis))

  = CLet name (letFloat beThis)
         (CSeq (letFloat this)
               (letFloat inThis))


letFloat (CLet x y z)
  = CLet x (letFloat y) (letFloat z)

letFloat (CSeq x y)
  = CSeq (letFloat x) (letFloat y)

letFloat expr
  = expr

||| Ensure that the lets have been floated to the top.
export
covering -- due to totality checker not liking recursive calls.
run : ChannelIR type
   -> LightClick (ChannelIR type)
run expr
  = if isNF expr
    then pure expr
    else run (letFloat expr)

-- [ EOF ]
