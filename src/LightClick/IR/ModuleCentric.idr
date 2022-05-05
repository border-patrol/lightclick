||| A module centric IR.
|||
||| Module    : ModuleCentric.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Module centric IRs follow the Graphviz approach to hardware description.
||| First, the modules are defined.
||| Second, the modules are connected together one channel at a time.
|||
module LightClick.IR.ModuleCentric

import Data.String
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import Language.SystemVerilog.Gates

import LightClick.Core

import LightClick.Types.Direction
import LightClick.Types.Necessity
import LightClick.Values

%default total

||| Types common to all IRs.
public export
data TyIR = PORT
          | UNIT
          | MODULE
          | CONN
          | DATA
          | CHAN
          | GATE

export
Show TyIR where
  show PORT   = "MTyPORT"
  show UNIT   = "MTyUNIT"
  show MODULE = "MTyMODULE"
  show CONN   = "MTyCONN"
  show DATA   = "MTyDATA"
  show CHAN   = "MTyCHAN"
  show GATE   = "MTyGATE"

public export
data ModuleIR : TyIR -> Type where
  MRef : (name : String)
      -> (type : TyIR)
              -> ModuleIR type

  MLet : {term : TyIR}
      -> (name : String)
      -> (beThis : ModuleIR (term))
      -> (inThis : ModuleIR (expr))
                -> ModuleIR (expr)

  MSeq : {a,b : TyIR}
      -> (doThis   : ModuleIR a)
      -> (thenThis : ModuleIR b)
                  -> ModuleIR b

  MEnd  : ModuleIR UNIT

  MPort : (label : String)
       -> (dir   : Direction)
       -> (n     : Necessity)
       -> (type  : ModuleIR DATA)
                -> ModuleIR PORT

  MModule : {n     : Nat}
         -> (ports : Vect (S n) (ModuleIR PORT))
                  -> ModuleIR MODULE

  MDataLogic : ModuleIR DATA

  MDataEnum : {n : Nat}
           -> (labels : Vect (S n) String)
                     -> ModuleIR DATA

  MDataArray : (type : ModuleIR DATA)
            -> (size : Nat)
                    -> ModuleIR DATA

  MDataStruct : {n      : Nat}
             -> (fields : Vect (S n)
                               (Pair String
                                     (ModuleIR DATA)))
                       -> ModuleIR DATA

  MDataUnion  : {n      : Nat}
             -> (fields : Vect (S n)
                               (Pair String
                                     (ModuleIR DATA)))
                        -> ModuleIR DATA

  MChan : (type : ModuleIR DATA)
               -> ModuleIR CHAN

  MIDX : (label : String)
      -> (mod   : ModuleIR MODULE)
               -> ModuleIR PORT

  MConn : {n      : Nat}
       -> (cname  : ModuleIR CHAN)
       -> (input  : ModuleIR PORT)
       -> (output : Vect (S n) $ ModuleIR PORT)
                 -> ModuleIR CONN

  MNot : (to,from : ModuleIR CHAN)
                 -> ModuleIR GATE

  MGate : {n    : Nat}
       -> (kind : TyGateComb)
       -> (to   : ModuleIR CHAN)
       -> (from : Vect (S (S n)) (ModuleIR CHAN))
               -> ModuleIR GATE

  MConnG : (this   : ModuleIR CHAN)
        -> (toThis : ModuleIR PORT)
                  -> ModuleIR CONN

  MNoOp : (dangle : ModuleIR PORT)
                 -> ModuleIR CONN

||| go from value (with proof of normal form) to moduleIR
public export
interp : TyValue -> TyIR
interp (PORT x) = PORT
interp UNIT = UNIT
interp (MODULE xs) = MODULE
interp CONN = CONN
interp DATA = DATA
interp CHAN = CHAN
interp GATE = GATE

mutual
  namespace Vect
    export
    convert : Vect n (Pair String (Value    DATA))
           -> Vect n (Pair String (ModuleIR DATA))
    convert = map (\(l,p) => (l, convert p))

  convert : Value type
          -> ModuleIR (interp type)
  convert (VRef name type)
    = MRef name (interp type)

  convert (VLet name beThis inThis)
    = MLet name (convert beThis) (convert inThis)

  convert (VSeq this thenThis)
    = MSeq (convert this) (convert thenThis)

  convert VEnd
    = MEnd

  convert (VPort label dir n type)
    = MPort label dir n (convert type)

  convert (VModule x)
    = MModule $ mapToVect (\p => (convert p)) x

  convert VDataLogic
    = MDataLogic

  convert (VDataEnum vs)
    = MDataEnum vs

  convert (VDataArray x k)
    = MDataArray (convert x) k

  convert (VDataStruct xs)
    = MDataStruct (convert xs)
  convert (VDataUnion  xs)
    = MDataUnion (convert xs)

  convert (VChan x)
    = MChan (convert x)

  convert (VIDX name x _)
    = MIDX name (convert x)

  convert (VConnD x y z)
    = MConn (convert x) (convert y) [convert z]

  convert (VConnFO x y z)
    = MConn (convert x) (convert y) (mapToVect (\p => convert p) z)

  convert (VNot o i)
    = MNot (convert o) (convert i)

  convert (VGate ty o ins)
    = MGate ty (convert o) (map convert ins)

  convert (VConnG c idx)
    = MConnG (convert c) (convert idx)

  convert (VNoOp _ p)
    = MNoOp (convert p)

||| Turn Values into module centric representations.
export
modularise : (v : Value type)
               -> LightClick (ModuleIR (interp type))
modularise
  = (pure . convert)

-- [ EOF ]
