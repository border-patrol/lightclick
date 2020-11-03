module LightClick.Error

import Control.WellFounded
import Data.Vect
import Data.Fin
import Data.Strings

import Toolkit.Data.Location

import LightClick.Types.Meta
import LightClick.IR.Channel.Normalise.Error

%default total

export
interface PrettyError (type : Type) where
  toString : type -> String

namespace Compatibility

  namespace Wire
    public export
    data Error = TypesDiffer

    export
    PrettyError Wire.Error where
      toString TypesDiffer = "Types are not compatible"

  namespace Sensitivity
    public export
    data Error = NoChangeFromHigh
               | NoChangeFromLow
               | NoChangeFromRising
               | NoChangeFromFalling

    export
    PrettyError (Sensitivity.Error) where
      toString NoChangeFromHigh    = "Cannot go from High to a different another sensative level."
      toString NoChangeFromLow     = "Cannot go from Low to a different another sensative level."
      toString NoChangeFromRising  = "Cannot go from Rising to a different another sensative level."
      toString NoChangeFromFalling = "Cannot go from Falling to a different another sensative level."

namespace Direction

  namespace Valid
    public export
    data Error = InputCannotSend | DirIsSame | OutputCannotReceive

    export
    PrettyError Direction.Valid.Error where
      toString InputCannotSend = "Input cannot send"
      toString DirIsSame = "Directions are the same"
      toString OutputCannotReceive = "Output ports cannot receive"

  namespace Safe
    public export
    data Error = VCError Direction.Valid.Error
               | PossibleFeedbackFromReceiver
               | PossibleFeedbackFromSender

    export
    PrettyError Direction.Safe.Error where
      toString (VCError x) = toString x
      toString PossibleFeedbackFromReceiver = "Possible Feedback from Receiver."
      toString PossibleFeedbackFromSender = "Possible Feedback from Sender."


namespace Compatibility

  namespace Data
    public export
    data Error : Type where
      Mismatch : Data.Error
      MismatchArrayLength : Data.Error
      MismatchArrayType   : (error : Data.Error) -> Data.Error
      MismatchStructureFieldType  : (position : Nat) -> (error : Data.Error) -> Data.Error
      MismatchStructureFieldLabel  : (position : Nat) -> (x,y : String) -> Data.Error
      MismatchStructureLength : Data.Error


    toString : (Data.Error) -> String
    toString Mismatch = "The data types are wildly different."
    toString MismatchArrayLength
      = "The arrays presented have different lengths."
    toString (MismatchArrayType x)
      = "The arrays presented have different types:\n" <+> toString x
    toString MismatchStructureLength
      = "The union/struct must have the same number of fields."
    toString (MismatchStructureFieldType pos err)
      = "The union/struct differs at position " <+> show pos <+> ". With Error:\n" <+> toString err
    toString (MismatchStructureFieldLabel pos x y)
      = "The labels differ at position " <+> show pos <+> ". With Error:\n" <+> show x <+> " & " <+> show y <+> "."

    export
    PrettyError (Data.Error ) where
      toString = Data.toString

  namespace Port


    public export
    data Error = InCompatSensitivity Sensitivity.Error
               | InCompatDirection   Direction.Safe.Error
               | InCompatWTypes      Wire.Error
               | InCompatDTypes      Data.Error


    export
    PrettyError Port.Error where

      toString (InCompatSensitivity err) = toString err
      toString (InCompatDirection   err) = toString err
      toString (InCompatWTypes      err) = toString err
      toString (InCompatDTypes      err) = toString err

  namespace PortList

    public export
    data Error = PListError Nat Compatibility.Port.Error

  namespace Mux

    public export
    data Error = CtrlNotSafe Compatibility.Port.Error | MuxNotSafe (Compatibility.PortList.Error)


namespace LightClick

  public export
  data FanTy = FANIN | FANOUT

  public export
  data Error = Err FileContext String
             | NotSupposedToHappen (Maybe String)
             | MetaTypeMismatch FileContext MTy MTy
             | IdentifierNotFound FileContext String
             | IdentifierAlreadyExists FileContext String
             | LabelAlreadyExists FileContext String (List String)
             | InvalidModuleIndex FileContext String (Vect (S n) String)
             | MetaTypeConstructionError FileContext MTy MTy
             | PortInUse FileContext String
             | ConstantsNotAllowed FileContext
             | UnSafeDirectConnection FileContext Compatibility.Port.Error
             | UnSafeFan FileContext FanTy Nat Compatibility.Port.Error
             | UnSafeMuxCtrl FileContext Compatibility.Port.Error
             | NormalisationError NError
             | UnusedPorts (List (String, List String))


  export
  PrettyError LightClick.Error where

    toString (Err loc msg) = unlines [show loc,msg]
    toString (NotSupposedToHappen Nothing)  = "Not Supposed to Happen."
    toString (NotSupposedToHappen (Just s)) = "Not Supposed to Happen. " <+> s
    toString (MetaTypeMismatch loc e g) =
        unlines [ show loc
                , "Type Mismatch:"
                , "\tExpected: " <+> show e
                , "\tGiven: " <+> show g]
    toString (IdentifierNotFound loc label) =
        unlines [ show loc
                , "Identifier " <+> show label <+> " not found."]
    toString (IdentifierAlreadyExists loc label) =
        unlines [ show loc
                , "Identifier " <+> show label <+> " already exists."]
    toString (LabelAlreadyExists loc label store) =
        unlines [ show loc
                , "The label " <+> show label <+> " already exists"
                , "It should *not* be one of: "
                , "\t" <+> show store]

    toString (InvalidModuleIndex loc label names) =
        unlines [ show loc
                , "The label " <+> show label <+> " is not a valid identifier."
                , "It should be one of: "
                , "\t" <+> show names]
    toString (MetaTypeConstructionError loc exp g) =
        unlines [ show loc
                , "Type Mismatch:"
                , "\tExpected: " <+> show' exp
                , "\tGiven: " <+> show g]
    toString (PortInUse loc s) =
        unlines [ show loc
                , "The port " <+> show s <+> " is already in use."]
    toString (ConstantsNotAllowed loc) =
        unlines [ show loc
                , "Constants are not allowed."
                ]

    toString (UnSafeDirectConnection loc msg) =
        unlines [ show loc
                , "Unsafe connection :"
                , "\t" <+> toString msg
                ]

    toString (UnSafeFan loc ty idx msg) =
         unlines [ show loc
                 , "Unsafe " <+> case ty of {FANIN => "Fan-IN."; FANOUT => "Fan-OUT."}
                 , "Wire #" <+> show idx <+> " is unsafe:"
                 , "\t" <+> toString msg
                 ]

    toString (UnSafeMuxCtrl loc msg) =
        unlines [ show loc
                , "Mux control wire is unsafe :"
                , "\t" <+> toString msg
                ]
    toString (NormalisationError err) =
        unlines ["Normalisation Error:"
                , show err
                ]

    toString (UnusedPorts Nil) = "Not supposed to happen: Unused port error is empty."
    toString (UnusedPorts ((n,ps)::Nil)) =
        unlines ["Unused port:"
                , "\t - " <+> (unwords [n, show ps])
                ]
    toString (UnusedPorts (p'::ps)) =
        unlines $ "Unused ports:" :: (map (\(n,ns) => "\t - " <+> (unwords [n, show ns])) (p'::ps))

  export
  Show LightClick.Error where
    show = (trim . toString)
