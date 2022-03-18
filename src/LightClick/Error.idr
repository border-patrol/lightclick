module LightClick.Error

import Control.WellFounded
import Data.Vect
import Data.Fin
import Data.String
import Data.List
import Data.List.Views

import Toolkit.Data.Location
import Toolkit.Data.DVect
import Toolkit.Text.Parser.Run

import LightClick.DSL.Lexer

import LightClick.Types
import LightClick.Connection
import LightClick.Types.Compatibility

import LightClick.IR.Channel.Normalise.Error
import LightClick.IR.Channel.MicroSV.Error

%default total

export
interface PrettyError (type : Type) where
  toString : type -> String

export
PrettyError Direction.Valid.Error where
  toString InputCannotSend = "Input cannot send"
  toString DirIsSame = "Directions are the same"
  toString OutputCannotReceive = "Output ports cannot receive"

export
PrettyError Direction.Safe.Error where
  toString (VCError x) = toString x
  toString PossibleFeedbackFromReceiver = "Possible Feedback from Receiver."
  toString PossibleFeedbackFromSender = "Possible Feedback from Sender."


export
Show Wire where
   show Data      = "data"
   show Address   = "address"
   show Clock     = "clock"
   show Reset     = "reset"
   show Info      = "info"
   show Interrupt = "interrupt"
   show Control   = "control"
   show General   = "general"

export
PrettyError Compatibility.Wire.Error where
  toString (TypesDiffer a b)
    = unlines [ "Incompatible intentions:"
              , "\tExpected:"
              , "\t\t" <+> show a
              , "\tGiven:"
              , "\t\t" <+> show b
              ]

export
Show Sensitivity where
 show High        = "high"
 show Low         = "low"
 show Rising      = "rising"
 show Falling     = "falling"
 show Insensitive = "insensitive"

export
PrettyError (Sensitivity.Error) where
  toString NoChangeFromHigh
    = "Cannot go from High to a different level."
  toString NoChangeFromLow
    = "Cannot go from Low to a different level."
  toString NoChangeFromRising
    = "Cannot go from Rising to a different level."
  toString NoChangeFromFalling
    = "Cannot go from Falling to a different level."

export
Show Necessity where
  show Required = "REQ"
  show Optional = "OPT"

namespace Compatibility

  namespace Data

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

    export
    PrettyError Port.Error where

      toString (InCompatSensitivity err) = toString err
      toString (InCompatDirection   err) = toString err
      toString (InCompatWTypes      err) = toString err
      toString (InCompatDTypes      err) = toString err

namespace Types


  Show TyRig where
    show None = show 0
    show One  = show 1
    show Tonne = "*"

  mutual
    kvsToString : Vect n (Pair String (Ty DATA)) -> String
    kvsToString [] = ""
    kvsToString ((l, ty) :: xs)
      = unwords [l, ":", toString ty]

    ksToListString : DVect String (Ty . PORT) n ps -> String
    ksToListString [] = ""
    ksToListString (ex :: []) = Types.toString ex
    ksToListString (ex :: (x :: rest))
      = Types.toString ex <+> "," <+> ksToListString (x::rest)

    export
    toString : forall a . Ty a -> String
    toString TyLogic
     = "logic"
    toString (TyArray type length)
     = toString type <+> "[" <+> show length <+> "]"

    toString (TyEnum kvs)
      = "enum {" <+> (unwords $ intersperse "," (toList kvs)) <+> "}"

    toString (TyStruct kvs)
      = "struct {" <+> kvsToString kvs <+> "}"

    toString (TyUnion kvs)
      = "union {" <+> kvsToString kvs <+> "}"

    toString TyUnit
      = "()"
    toString TyConn
      = "conn"

    toString TyGate
      = "gate"

    toString (TyPort label dir sense wty n type)
      = unwords [ label
                , ":"
                , "port ("
                , show dir
                , show sense
                , show wty
                , show n
                , toString type

                , ")"]

    toString (TyModule xs)
      = "module ( " <+> (ksToListString xs) <+> ")"

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
             | UnSafeDirectConnection FileContext Port.Error
             | UnSafeFan FileContext FanTy Nat Port.Error
             | UnSafeMuxCtrl FileContext Port.Error
             | NormalisationError Normalise.Error
             | MicroSVError TError
             | UnusedPorts (List (String, List String))
             | Mismatch FileContext (Ty a) (Ty b)
             | SeqError
             | BindError
             | FileError String (ParseError Token)
             | Nest LightClick.Error LightClick.Error


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
                , "Unsafe connection with " <+> toString msg
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

    toString (MicroSVError err) =
        unlines ["MicroSV Transformation Error:"
                , show err
                ]

    toString (UnusedPorts Nil) = "Not supposed to happen: Unused port error is empty."
    toString (UnusedPorts ((n,ps)::Nil)) =
        unlines ["Unused port:"
                , "\t - " <+> (unwords [n, show ps])
                ]
    toString (UnusedPorts (p'::ps)) =
        unlines $ "Unused ports:" :: (map (\(n,ns) => "\t - " <+> (unwords [n, show ns])) (p'::ps))

    toString (Mismatch loc e g) =
        unlines [ show loc
                , "Connection mismatch when trying to connect:"
                , "\tthis:\n\t\t" <+> toString e
                , "\tthat:\n\t\t" <+> toString g]

    toString SeqError
      = "Only Gates and Connections can be sequenced."

    toString BindError
      = "Only datatypes and modules can be bound."

    toString (FileError str err)
      = show err
    toString (Nest x y)
      = unlines [toString x, "Specifically:", toString y]

  export
  Show LightClick.Error where
    show = (trim . toString)
