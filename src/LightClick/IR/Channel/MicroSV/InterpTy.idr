module LightClick.IR.Channel.MicroSV.InterpTy

import LightClick.IR.ModuleCentric
import LightClick.Types.Direction

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Direction



%default total

total
export
interpDir : Types.Direction.Direction -> SystemVerilog.Direction.Direction
interpDir IN = IN
interpDir OUT = OUT
interpDir INOUT = INOUT

public export
data InterpTy : TyIR -> Ty -> Type where
  PP : (x : String) -> InterpTy PORT   (PORT x)
  UU : InterpTy UNIT   UNIT
  MM : (xs : List String) -> InterpTy MODULE (MODULE xs)
  CM : (xs : List String) -> InterpTy CONN   (MINST xs)
  DD : InterpTy DATA   DATA
  CC : InterpTy CHAN   CHAN

public export
getTy : {ty : Ty} -> InterpTy type ty -> Ty
getTy {ty} _ = ty

portMod : InterpTy PORT (MODULE xs) -> Void
portMod (PP _) impossible
portMod UU impossible
portMod (MM _) impossible
portMod (CM _) impossible
portMod DD impossible
portMod CC impossible

portDat : InterpTy PORT DATA -> Void
portDat (PP _) impossible
portDat UU impossible
portDat (MM _) impossible
portDat (CM _) impossible
portDat DD impossible
portDat CC impossible

portCha : InterpTy PORT CHAN -> Void
portCha (PP _) impossible
portCha UU impossible
portCha (MM _) impossible
portCha (CM _) impossible
portCha DD impossible
portCha CC impossible

portMIn : InterpTy PORT (MINST xs) -> Void
portMIn (PP _) impossible
portMIn UU impossible
portMIn (MM _) impossible
portMIn (CM _) impossible
portMIn DD impossible
portMIn CC impossible

portUni : InterpTy PORT UNIT -> Void
portUni (PP _) impossible
portUni UU impossible
portUni (MM _) impossible
portUni (CM _) impossible
portUni DD impossible
portUni CC impossible

portTyp : InterpTy PORT TYPE -> Void
portTyp (PP _) impossible
portTyp UU impossible
portTyp (MM _) impossible
portTyp (CM _) impossible
portTyp DD impossible
portTyp CC impossible

unitMod : InterpTy UNIT (MODULE xs) -> Void
unitMod (PP _) impossible
unitMod UU impossible
unitMod (MM _) impossible
unitMod (CM _) impossible
unitMod DD impossible
unitMod CC impossible

unitDat : InterpTy UNIT DATA -> Void
unitDat (PP _) impossible
unitDat UU impossible
unitDat (MM _) impossible
unitDat (CM _) impossible
unitDat DD impossible
unitDat CC impossible

unitCh : InterpTy UNIT CHAN -> Void
unitCh (PP _) impossible
unitCh UU impossible
unitCh (MM _) impossible
unitCh (CM _) impossible
unitCh DD impossible
unitCh CC impossible

unitPor : InterpTy UNIT (PORT x) -> Void
unitPor (PP _) impossible
unitPor UU impossible
unitPor (MM _) impossible
unitPor (CM _) impossible
unitPor DD impossible
unitPor CC impossible

unitMIn : InterpTy UNIT (MINST xs) -> Void
unitMIn (PP _) impossible
unitMIn UU impossible
unitMIn (MM _) impossible
unitMIn (CM _) impossible
unitMIn DD impossible
unitMIn CC impossible

unitTyp : InterpTy UNIT TYPE -> Void
unitTyp (PP _) impossible
unitTyp UU impossible
unitTyp (MM _) impossible
unitTyp (CM _) impossible
unitTyp DD impossible
unitTyp CC impossible

moduleUni : InterpTy MODULE UNIT -> Void
moduleUni (PP _) impossible
moduleUni UU impossible
moduleUni (MM _) impossible
moduleUni (CM _) impossible
moduleUni DD impossible
moduleUni CC impossible

moduleDat : InterpTy MODULE DATA -> Void
moduleDat (PP _) impossible
moduleDat UU impossible
moduleDat (MM _) impossible
moduleDat (CM _) impossible
moduleDat DD impossible
moduleDat CC impossible

moduleCh : InterpTy MODULE CHAN -> Void
moduleCh (PP _) impossible
moduleCh UU impossible
moduleCh (MM _) impossible
moduleCh (CM _) impossible
moduleCh DD impossible
moduleCh CC impossible

modulePor : InterpTy MODULE (PORT x) -> Void
modulePor (PP _) impossible
modulePor UU impossible
modulePor (MM _) impossible
modulePor (CM _) impossible
modulePor DD impossible
modulePor CC impossible

moduleMIn : InterpTy MODULE (MINST xs) -> Void
moduleMIn (PP _) impossible
moduleMIn UU impossible
moduleMIn (MM _) impossible
moduleMIn (CM _) impossible
moduleMIn DD impossible
moduleMIn CC impossible

moduleTyp : InterpTy MODULE TYPE -> Void
moduleTyp (PP _) impossible
moduleTyp UU impossible
moduleTyp (MM _) impossible
moduleTyp (CM _) impossible
moduleTyp DD impossible
moduleTyp CC impossible

dataMod : InterpTy DATA (MODULE xs) -> Void
dataMod (PP _) impossible
dataMod UU impossible
dataMod (MM _) impossible
dataMod (CM _) impossible
dataMod DD impossible
dataMod CC impossible

dataUni : InterpTy DATA UNIT -> Void
dataUni (PP _) impossible
dataUni UU impossible
dataUni (MM _) impossible
dataUni (CM _) impossible
dataUni DD impossible
dataUni CC impossible

dataCh : InterpTy DATA CHAN -> Void
dataCh (PP _) impossible
dataCh UU impossible
dataCh (MM _) impossible
dataCh (CM _) impossible
dataCh DD impossible
dataCh CC impossible

dataPor : InterpTy DATA (PORT x) -> Void
dataPor (PP _) impossible
dataPor UU impossible
dataPor (MM _) impossible
dataPor (CM _) impossible
dataPor DD impossible
dataPor CC impossible

dataMIn : InterpTy DATA (MINST xs) -> Void
dataMIn (PP _) impossible
dataMIn UU impossible
dataMIn (MM _) impossible
dataMIn (CM _) impossible
dataMIn DD impossible
dataMIn CC impossible

dataTyp : InterpTy DATA TYPE -> Void
dataTyp (PP _) impossible
dataTyp UU impossible
dataTyp (MM _) impossible
dataTyp (CM _) impossible
dataTyp DD impossible
dataTyp CC impossible

connMod : InterpTy CONN (MODULE xs) -> Void
connMod (PP _) impossible
connMod UU impossible
connMod (MM _) impossible
connMod (CM _) impossible
connMod DD impossible
connMod CC impossible

connUni : InterpTy CONN UNIT -> Void
connUni (PP _) impossible
connUni UU impossible
connUni (MM _) impossible
connUni (CM _) impossible
connUni DD impossible
connUni CC impossible

connCh : InterpTy CONN CHAN -> Void
connCh (PP _) impossible
connCh UU impossible
connCh (MM _) impossible
connCh (CM _) impossible
connCh DD impossible
connCh CC impossible

connPor : InterpTy CONN (PORT x) -> Void
connPor (PP _) impossible
connPor UU impossible
connPor (MM _) impossible
connPor (CM _) impossible
connPor DD impossible
connPor CC impossible

connTyp : InterpTy CONN TYPE -> Void
connTyp (PP _) impossible
connTyp UU impossible
connTyp (MM _) impossible
connTyp (CM _) impossible
connTyp DD impossible
connTyp CC impossible

connDat : InterpTy CONN DATA -> Void
connDat (PP _) impossible
connDat UU impossible
connDat (MM _) impossible
connDat (CM _) impossible
connDat DD impossible
connDat CC impossible

chanMod : InterpTy CHAN (MODULE xs) -> Void
chanMod (PP _) impossible
chanMod UU impossible
chanMod (MM _) impossible
chanMod (CM _) impossible
chanMod DD impossible
chanMod CC impossible

chanUni : InterpTy CHAN UNIT -> Void
chanUni (PP _) impossible
chanUni UU impossible
chanUni (MM _) impossible
chanUni (CM _) impossible
chanUni DD impossible
chanUni CC impossible

chanPor : InterpTy CHAN (PORT x) -> Void
chanPor (PP _) impossible
chanPor UU impossible
chanPor (MM _) impossible
chanPor (CM _) impossible
chanPor DD impossible
chanPor CC impossible

chanTyp : InterpTy CHAN TYPE -> Void
chanTyp (PP _) impossible
chanTyp UU impossible
chanTyp (MM _) impossible
chanTyp (CM _) impossible
chanTyp DD impossible
chanTyp CC impossible

chanDat : InterpTy CHAN DATA -> Void
chanDat (PP _) impossible
chanDat UU impossible
chanDat (MM _) impossible
chanDat (CM _) impossible
chanDat DD impossible
chanDat CC impossible

chanMIn : InterpTy CHAN (MINST xs) -> Void
chanMIn (PP _) impossible
chanMIn UU impossible
chanMIn (MM _) impossible
chanMIn (CM _) impossible
chanMIn DD impossible
chanMIn CC impossible

export
interpTy : (ty : TyIR)
        -> (type : Ty)
        -> Dec (InterpTy ty type)
interpTy PORT (MODULE xs) = No portMod
interpTy PORT DATA = No portDat
interpTy PORT CHAN = No portCha
interpTy PORT (PORT x) = Yes (PP x)
interpTy PORT (MINST xs) = No portMIn
interpTy PORT UNIT = No portUni
interpTy PORT TYPE = No portTyp

interpTy UNIT (MODULE xs) = No unitMod
interpTy UNIT DATA = No unitDat
interpTy UNIT CHAN = No unitCh
interpTy UNIT (PORT x) = No unitPor
interpTy UNIT (MINST xs) = No unitMIn
interpTy UNIT UNIT = Yes UU
interpTy UNIT TYPE = No unitTyp

interpTy MODULE (MODULE xs) = Yes (MM xs)
interpTy MODULE DATA = No moduleDat
interpTy MODULE CHAN = No moduleCh
interpTy MODULE (PORT x) = No modulePor
interpTy MODULE (MINST xs) = No moduleMIn
interpTy MODULE UNIT = No moduleUni
interpTy MODULE TYPE = No moduleTyp

interpTy CONN (MODULE xs) = No connMod
interpTy CONN DATA = No connDat
interpTy CONN CHAN = No connCh
interpTy CONN (PORT x) = No connPor
interpTy CONN (MINST xs) = Yes (CM xs)
interpTy CONN UNIT = No connUni
interpTy CONN TYPE = No connTyp

interpTy DATA (MODULE xs) = No dataMod
interpTy DATA DATA = Yes DD
interpTy DATA CHAN = No dataCh
interpTy DATA (PORT x) = No dataPor
interpTy DATA (MINST xs) = No dataMIn
interpTy DATA UNIT = No dataUni
interpTy DATA TYPE = No dataTyp

interpTy CHAN (MODULE xs) = No chanMod
interpTy CHAN DATA = No chanDat
interpTy CHAN CHAN = Yes CC
interpTy CHAN (PORT x) = No chanPor
interpTy CHAN (MINST xs) = No chanMIn
interpTy CHAN UNIT = No chanUni
interpTy CHAN TYPE = No chanTyp

namespace TyIR
  public export
  data IsGlobal : TyIR -> Type where
    IsDeclM : IsGlobal MODULE
    IsDeclD : IsGlobal DATA

  public export
  data IsLocal : TyIR -> Type where
    IsInstM : IsLocal CONN
    IsInstC : IsLocal CHAN

  public export
  data Bindable : TyIR -> Type where
    IsDecl : IsGlobal type -> Bindable type
    IsLet  : IsLocal type  -> Bindable type
    Unbindable : TyIR.Bindable type

  export
  isBindable : (type : TyIR) -> Bindable type
  isBindable PORT = Unbindable
  isBindable UNIT = Unbindable
  isBindable MODULE = IsDecl IsDeclM
  isBindable CONN = IsLet IsInstM
  isBindable DATA = IsDecl IsDeclD
  isBindable CHAN = IsLet IsInstC

-- --------------------------------------------------------------------- [ EOF ]
