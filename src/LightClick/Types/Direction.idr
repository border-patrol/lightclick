module LightClick.Types.Direction

import Decidable.Equality

import Toolkit.Decidable.Informative

import LightClick.Error

%default total

public export
data Direction = IN | OUT | INOUT

export
Show Direction where
  show IN = "(IN)"
  show OUT = "(OUT)"
  show INOUT = "(INOUT)"

inNotOut : (IN = OUT) -> Void
inNotOut Refl impossible

inNotInOut : (IN = INOUT) -> Void
inNotInOut Refl impossible

outNotInOut : (OUT = INOUT) -> Void
outNotInOut Refl impossible

export
DecEq Direction where
  decEq IN IN = Yes Refl
  decEq IN OUT = No inNotOut
  decEq IN INOUT = No inNotInOut

  decEq OUT IN = No (negEqSym inNotOut)
  decEq OUT OUT = Yes Refl
  decEq OUT INOUT = No outNotInOut

  decEq INOUT IN = No (negEqSym inNotInOut)
  decEq INOUT OUT = No (negEqSym outNotInOut)
  decEq INOUT INOUT = Yes Refl

namespace Valid

  public export
  data Valid : (src,dest : Direction) -> Type where
    VOI : Valid OUT   IN
    VBI : Valid INOUT IN
    VOB : Valid OUT   INOUT
    VBB : Valid INOUT INOUT

  dirIsLR : Valid IN dest -> Void
  dirIsLR VOI impossible
  dirIsLR VBI impossible
  dirIsLR VOB impossible
  dirIsLR VBB impossible

  dirAreSame : Valid OUT OUT -> Void
  dirAreSame VOI impossible
  dirAreSame VBI impossible
  dirAreSame VOB impossible
  dirAreSame VBB impossible

  dirIsLR' : Valid INOUT OUT -> Void
  dirIsLR' VOI impossible
  dirIsLR' VBI impossible
  dirIsLR' VOB impossible
  dirIsLR' VBB impossible

  export
  valid : (src, dest : Direction) -> DecInfo Direction.Valid.Error (Valid src dest)
  valid IN dest = No InputCannotSend dirIsLR
  valid OUT dest with (dest)
    valid OUT dest | IN = Yes VOI
    valid OUT dest | OUT = No DirIsSame dirAreSame
    valid OUT dest | INOUT = Yes VOB

  valid INOUT dest with (dest)
    valid INOUT dest | IN = Yes VBI
    valid INOUT dest | OUT = No OutputCannotReceive (dirIsLR')
    valid INOUT dest | INOUT = Yes VBB


namespace Safe

  public export
  data Safe : (src,dest : Direction) -> Type where
    SOI : Safe OUT   IN
    SBI : Safe INOUT IN
    SBB : Safe INOUT INOUT

  safeDirCannotIn : Safe IN dest -> Void
  safeDirCannotIn SOI impossible
  safeDirCannotIn SBI impossible
  safeDirCannotIn SBB impossible

  safeDirNotOO : Safe OUT OUT -> Void
  safeDirNotOO SOI impossible
  safeDirNotOO SBI impossible
  safeDirNotOO SBB impossible

  safeDirNoFeedbackOO : Safe OUT INOUT -> Void
  safeDirNoFeedbackOO SOI impossible
  safeDirNoFeedbackOO SBI impossible
  safeDirNoFeedbackOO SBB impossible

  safeDirNoFeedbackBO : Safe INOUT OUT -> Void
  safeDirNoFeedbackBO SOI impossible
  safeDirNoFeedbackBO SBI impossible
  safeDirNoFeedbackBO SBB impossible

  export
  safe : (src, dest : Direction) -> DecInfo Direction.Safe.Error (Safe src dest)
  safe IN dest = No (VCError InputCannotSend) safeDirCannotIn
  safe OUT dest with (dest)
    safe OUT dest | IN = Yes SOI
    safe OUT dest | OUT = No (VCError DirIsSame) safeDirNotOO
    safe OUT dest | INOUT = No PossibleFeedbackFromReceiver safeDirNoFeedbackOO

  safe INOUT dest with (dest)
    safe INOUT dest | IN = Yes SBI
    safe INOUT dest | OUT = No PossibleFeedbackFromSender safeDirNoFeedbackBO
    safe INOUT dest | INOUT = Yes SBB
