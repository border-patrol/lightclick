module LightClick.IR.ModuleCentric

import Data.Vect
import Data.DList
import Data.DVect

import LightClick.Error
import LightClick.Types
import LightClick.Values

%default total

public export
data TyIR = PORT
          | UNIT
          | MODULE
          | CONN
          | DATA
          | CHAN

export
Show TyIR where
  show PORT   = "MTyPORT"
  show UNIT   = "MTyUNIT"
  show MODULE = "MTyMODULE"
  show CONN   = "MTyCONN"
  show DATA   = "MTyDATA"
  show CHAN   = "MTyCHAN"

public export
data ModuleIR : TyIR -> Type where
  MRef : (name : String) -> (type : TyIR) -> ModuleIR type
  MLet : {term : TyIR} -> (name : String)
      -> (beThis : ModuleIR (term))
      -> (inThis : ModuleIR (expr)) -> ModuleIR (expr)

  MSeq : {a,b : TyIR} -> (doThis   : ModuleIR a)
      -> (thenThis : ModuleIR b) -> ModuleIR b

  MEnd  : ModuleIR UNIT

  MPort : (label : String)
       -> (dir   : Direction)
       -> (type  : ModuleIR DATA) -> ModuleIR PORT

  MModule : Vect (S n) (ModuleIR PORT) -> ModuleIR MODULE

  MDataLogic : ModuleIR DATA
  MDataArray : ModuleIR DATA -> Nat -> ModuleIR DATA
  MDataStruct : {n : Nat} -> Vect (S n) (Pair String (ModuleIR DATA)) -> ModuleIR DATA
  MDataUnion  : {n : Nat} -> Vect (S n) (Pair String (ModuleIR DATA)) -> ModuleIR DATA

  MChan : ModuleIR DATA -> ModuleIR CHAN

  MIDX : (label : String)
      -> ModuleIR MODULE
      -> ModuleIR PORT
      -> ModuleIR PORT

  MConn : (cname  : ModuleIR CHAN)
       -> (input  : ModuleIR PORT)
       -> (output : Vect (S n) $ ModuleIR PORT)
       -> ModuleIR CONN

-- go from value (with proof of normal form) to moduleIR
public export
interp : TyValue -> TyIR
interp (PORT x) = PORT
interp UNIT = UNIT
interp (MODULE xs) = MODULE
interp CONN = CONN
interp DATA = DATA
interp CHAN = CHAN

covering
convert : Value type -> ModuleIR (interp type)
convert (VRef name type) = MRef name (interp type)
convert (VLet name beThis inThis) = MLet name (convert beThis) (convert inThis)
convert (VSeq this thenThis) = MSeq (convert this) (convert thenThis)
convert VEnd = MEnd

convert (VPort label dir type) = MPort label dir (convert type)
convert (VModule x) = MModule $ mapToVect (\p => (convert p)) x

convert VDataLogic = MDataLogic
convert (VDataArray x k) = MDataArray (convert x) k
convert (VDataStruct xs) = MDataStruct $ map (\(l,p) => (l,convert p)) xs
convert (VDataUnion xs) = MDataUnion $ map (\(l,p) => (l,convert p)) xs

convert (VChan x) = MChan (convert x)
convert (VIDX name x y) = MIDX name (convert x) (convert y)

convert (VConnD x y z) = MConn (convert x) (convert y) [convert z]
convert (VConnFO x y z) = MConn (convert x) (convert y) (mapToVect (\p => convert p) z)

covering
export
runConvert : Value type -> ModuleIR (interp type)
runConvert = convert

covering
showM : ModuleIR type -> String
showM (MRef name type) =
  "(MRef " <+> show name <+> ")"

showM (MLet x y z) =
   "(MLet "
     <+> show x <+> " "
     <+> showM y <+> " "
     <+> showM z
     <+> ")"

showM (MSeq x y) =
    "(MSeq "
      <+> showM x <+> " "
      <+> showM y
      <+> ")"
showM MEnd = "(MEnd)"

showM (MPort x y z) =
    "(MPort "
      <+> show x <+> " "
      <+> show y <+> " "
      <+> showM z <+> " "
      <+> ")"

showM (MModule x) =
    "(MModule "
      <+> show (map showM x)
      <+> ")"

showM MDataLogic = "(MTyLogic)"

showM (MDataArray x k) =
  "(MTyArray "
    <+> showM x <+> " "
    <+> show k
    <+> ")"

showM (MDataStruct {n} xs) = "(MTyStruct " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showM c <+> ")") xs


showM (MDataUnion {n} xs) = "(TyUnion " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showM c <+> ")") xs

showM (MChan x) = "(MChan " <+> showM x <+> ")"

showM (MIDX x y z) =
    "(MIndex "
       <+> show x <+> " "
       <+> showM y <+> " "
       <+> showM z
       <+> ")"

showM (MConn x y ps) =
    "(MDConn "
      <+> showM x <+> " "
      <+> showM y <+> " "
      <+> show (map showM ps)
      <+> ")"

export
Show (ModuleIR type) where
  show = assert_total showM
