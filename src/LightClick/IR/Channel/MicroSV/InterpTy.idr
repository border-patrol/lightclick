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
  GG : InterpTy GATE   GINST

public export
getTy : {ty : Ty} -> InterpTy type ty -> Ty
getTy {ty} _ = ty


-- Ports

portMod : InterpTy PORT (MODULE xs) -> Void
portMod (PP _) impossible
portMod UU impossible
portMod (MM _) impossible
portMod (CM _) impossible
portMod DD impossible
portMod CC impossible
portMod GG impossible

portDat : InterpTy PORT DATA -> Void
portDat (PP _) impossible
portDat UU impossible
portDat (MM _) impossible
portDat (CM _) impossible
portDat DD impossible
portDat CC impossible
portDat GG impossible

portCha : InterpTy PORT CHAN -> Void
portCha (PP _) impossible
portCha UU impossible
portCha (MM _) impossible
portCha (CM _) impossible
portCha DD impossible
portCha CC impossible
portCha GG impossible

portMIn : InterpTy PORT (MINST xs) -> Void
portMIn (PP _) impossible
portMIn UU impossible
portMIn (MM _) impossible
portMIn (CM _) impossible
portMIn DD impossible
portMIn CC impossible
portMIn GG impossible

portUni : InterpTy PORT UNIT -> Void
portUni (PP _) impossible
portUni UU impossible
portUni (MM _) impossible
portUni (CM _) impossible
portUni DD impossible
portUni CC impossible
portUni GG impossible

portTyp : InterpTy PORT TYPE -> Void
portTyp (PP _) impossible
portTyp UU impossible
portTyp (MM _) impossible
portTyp (CM _) impossible
portTyp DD impossible
portTyp CC impossible
portTyp GG impossible

portGat : InterpTy PORT GATE -> Void
portGat (PP _) impossible
portGat UU impossible
portGat (MM _) impossible
portGat (CM _) impossible
portGat DD impossible
portGat CC impossible
portGat GG impossible

portGinst : InterpTy PORT GINST -> Void
portGinst (PP _) impossible
portGinst UU impossible
portGinst (MM _) impossible
portGinst (CM _) impossible
portGinst DD impossible
portGinst CC impossible
portGinst GG impossible

-- Unit

unitMod : InterpTy UNIT (MODULE xs) -> Void
unitMod (PP _) impossible
unitMod UU impossible
unitMod (MM _) impossible
unitMod (CM _) impossible
unitMod DD impossible
unitMod CC impossible
unitMod GG impossible

unitDat : InterpTy UNIT DATA -> Void
unitDat (PP _) impossible
unitDat UU impossible
unitDat (MM _) impossible
unitDat (CM _) impossible
unitDat DD impossible
unitDat CC impossible
unitDat GG impossible

unitCh : InterpTy UNIT CHAN -> Void
unitCh (PP _) impossible
unitCh UU impossible
unitCh (MM _) impossible
unitCh (CM _) impossible
unitCh DD impossible
unitCh CC impossible
unitCh GG impossible

unitPor : InterpTy UNIT (PORT x) -> Void
unitPor (PP _) impossible
unitPor UU impossible
unitPor (MM _) impossible
unitPor (CM _) impossible
unitPor DD impossible
unitPor CC impossible
unitPor GG impossible

unitMIn : InterpTy UNIT (MINST xs) -> Void
unitMIn (PP _) impossible
unitMIn UU impossible
unitMIn (MM _) impossible
unitMIn (CM _) impossible
unitMIn DD impossible
unitMIn CC impossible
unitMIn GG impossible

unitTyp : InterpTy UNIT TYPE -> Void
unitTyp (PP _) impossible
unitTyp UU impossible
unitTyp (MM _) impossible
unitTyp (CM _) impossible
unitTyp DD impossible
unitTyp CC impossible
unitTyp GG impossible

unitGat : InterpTy UNIT GATE -> Void
unitGat (PP _) impossible
unitGat UU impossible
unitGat (MM _) impossible
unitGat (CM _) impossible
unitGat DD impossible
unitGat CC impossible
unitGat GG impossible

unitGinst : InterpTy UNIT GINST -> Void
unitGinst (PP _) impossible
unitGinst UU impossible
unitGinst (MM _) impossible
unitGinst (CM _) impossible
unitGinst DD impossible
unitGinst CC impossible
unitGinst GG impossible

-- Module

moduleUni : InterpTy MODULE UNIT -> Void
moduleUni (PP _) impossible
moduleUni UU impossible
moduleUni (MM _) impossible
moduleUni (CM _) impossible
moduleUni DD impossible
moduleUni CC impossible
moduleUni GG impossible

moduleDat : InterpTy MODULE DATA -> Void
moduleDat (PP _) impossible
moduleDat UU impossible
moduleDat (MM _) impossible
moduleDat (CM _) impossible
moduleDat DD impossible
moduleDat CC impossible
moduleDat GG impossible

moduleCh : InterpTy MODULE CHAN -> Void
moduleCh (PP _) impossible
moduleCh UU impossible
moduleCh (MM _) impossible
moduleCh (CM _) impossible
moduleCh DD impossible
moduleCh CC impossible
moduleCh GG impossible

modulePor : InterpTy MODULE (PORT x) -> Void
modulePor (PP _) impossible
modulePor UU impossible
modulePor (MM _) impossible
modulePor (CM _) impossible
modulePor DD impossible
modulePor CC impossible
modulePor GG impossible

moduleMIn : InterpTy MODULE (MINST xs) -> Void
moduleMIn (PP _) impossible
moduleMIn UU impossible
moduleMIn (MM _) impossible
moduleMIn (CM _) impossible
moduleMIn DD impossible
moduleMIn CC impossible
moduleMIn GG impossible

moduleTyp : InterpTy MODULE TYPE -> Void
moduleTyp (PP _) impossible
moduleTyp UU impossible
moduleTyp (MM _) impossible
moduleTyp (CM _) impossible
moduleTyp DD impossible
moduleTyp CC impossible
moduleTyp GG impossible

moduleGat : InterpTy MODULE GATE -> Void
moduleGat (PP _) impossible
moduleGat UU impossible
moduleGat (MM _) impossible
moduleGat (CM _) impossible
moduleGat DD impossible
moduleGat CC impossible
moduleGat GG impossible

moduleGinst : InterpTy MODULE GINST -> Void
moduleGinst (PP _) impossible
moduleGinst UU impossible
moduleGinst (MM _) impossible
moduleGinst (CM _) impossible
moduleGinst DD impossible
moduleGinst CC impossible
moduleGinst GG impossible

-- Data

dataMod : InterpTy DATA (MODULE xs) -> Void
dataMod (PP _) impossible
dataMod UU impossible
dataMod (MM _) impossible
dataMod (CM _) impossible
dataMod DD impossible
dataMod CC impossible
dataMod GG impossible

dataUni : InterpTy DATA UNIT -> Void
dataUni (PP _) impossible
dataUni UU impossible
dataUni (MM _) impossible
dataUni (CM _) impossible
dataUni DD impossible
dataUni CC impossible
dataUni GG impossible

dataCh : InterpTy DATA CHAN -> Void
dataCh (PP _) impossible
dataCh UU impossible
dataCh (MM _) impossible
dataCh (CM _) impossible
dataCh DD impossible
dataCh CC impossible
dataCh GG impossible

dataPor : InterpTy DATA (PORT x) -> Void
dataPor (PP _) impossible
dataPor UU impossible
dataPor (MM _) impossible
dataPor (CM _) impossible
dataPor DD impossible
dataPor CC impossible
dataPor GG impossible

dataMIn : InterpTy DATA (MINST xs) -> Void
dataMIn (PP _) impossible
dataMIn UU impossible
dataMIn (MM _) impossible
dataMIn (CM _) impossible
dataMIn DD impossible
dataMIn CC impossible
dataMIn GG impossible

dataTyp : InterpTy DATA TYPE -> Void
dataTyp (PP _) impossible
dataTyp UU impossible
dataTyp (MM _) impossible
dataTyp (CM _) impossible
dataTyp DD impossible
dataTyp CC impossible
dataTyp GG impossible

dataGat : InterpTy DATA GATE -> Void
dataGat (PP _) impossible
dataGat UU impossible
dataGat (MM _) impossible
dataGat (CM _) impossible
dataGat DD impossible
dataGat CC impossible
dataGat GG impossible

dataGinst : InterpTy DATA GINST -> Void
dataGinst (PP _) impossible
dataGinst UU impossible
dataGinst (MM _) impossible
dataGinst (CM _) impossible
dataGinst DD impossible
dataGinst CC impossible
dataGinst GG impossible

-- Conns

connMod : InterpTy CONN (MODULE xs) -> Void
connMod (PP _) impossible
connMod UU impossible
connMod (MM _) impossible
connMod (CM _) impossible
connMod DD impossible
connMod CC impossible
connMod GG impossible

connUni : InterpTy CONN UNIT -> Void
connUni (PP _) impossible
connUni UU impossible
connUni (MM _) impossible
connUni (CM _) impossible
connUni DD impossible
connUni CC impossible
connUni GG impossible

connCh : InterpTy CONN CHAN -> Void
connCh (PP _) impossible
connCh UU impossible
connCh (MM _) impossible
connCh (CM _) impossible
connCh DD impossible
connCh CC impossible
connCh GG impossible

connPor : InterpTy CONN (PORT x) -> Void
connPor (PP _) impossible
connPor UU impossible
connPor (MM _) impossible
connPor (CM _) impossible
connPor DD impossible
connPor CC impossible
connPor GG impossible

connTyp : InterpTy CONN TYPE -> Void
connTyp (PP _) impossible
connTyp UU impossible
connTyp (MM _) impossible
connTyp (CM _) impossible
connTyp DD impossible
connTyp CC impossible
connTyp GG impossible

connDat : InterpTy CONN DATA -> Void
connDat (PP _) impossible
connDat UU impossible
connDat (MM _) impossible
connDat (CM _) impossible
connDat DD impossible
connDat CC impossible
connDat GG impossible

connGat : InterpTy CONN GATE -> Void
connGat (PP _) impossible
connGat UU impossible
connGat (MM _) impossible
connGat (CM _) impossible
connGat DD impossible
connGat CC impossible
connGat GG impossible

connGinst : InterpTy CONN GINST -> Void
connGinst (PP _) impossible
connGinst UU impossible
connGinst (MM _) impossible
connGinst (CM _) impossible
connGinst DD impossible
connGinst CC impossible
connGinst GG impossible

-- Channel

chanMod : InterpTy CHAN (MODULE xs) -> Void
chanMod (PP _) impossible
chanMod UU impossible
chanMod (MM _) impossible
chanMod (CM _) impossible
chanMod DD impossible
chanMod CC impossible
chanMod GG impossible

chanUni : InterpTy CHAN UNIT -> Void
chanUni (PP _) impossible
chanUni UU impossible
chanUni (MM _) impossible
chanUni (CM _) impossible
chanUni DD impossible
chanUni CC impossible
chanUni GG impossible

chanPor : InterpTy CHAN (PORT x) -> Void
chanPor (PP _) impossible
chanPor UU impossible
chanPor (MM _) impossible
chanPor (CM _) impossible
chanPor DD impossible
chanPor CC impossible
chanPor GG impossible

chanTyp : InterpTy CHAN TYPE -> Void
chanTyp (PP _) impossible
chanTyp UU impossible
chanTyp (MM _) impossible
chanTyp (CM _) impossible
chanTyp DD impossible
chanTyp CC impossible
chanTyp GG impossible

chanDat : InterpTy CHAN DATA -> Void
chanDat (PP _) impossible
chanDat UU impossible
chanDat (MM _) impossible
chanDat (CM _) impossible
chanDat DD impossible
chanDat CC impossible
chanDat GG impossible

chanMIn : InterpTy CHAN (MINST xs) -> Void
chanMIn (PP _) impossible
chanMIn UU impossible
chanMIn (MM _) impossible
chanMIn (CM _) impossible
chanMIn DD impossible
chanMIn CC impossible
chanMIn GG impossible

chanGat : InterpTy CHAN GATE -> Void
chanGat (PP _) impossible
chanGat UU impossible
chanGat (MM _) impossible
chanGat (CM _) impossible
chanGat DD impossible
chanGat CC impossible
chanGat GG impossible

chanGinst : InterpTy CHAN GINST -> Void
chanGinst (PP _) impossible
chanGinst UU impossible
chanGinst (MM _) impossible
chanGinst (CM _) impossible
chanGinst DD impossible
chanGinst CC impossible
chanGinst GG impossible

-- Channel

gateMod : InterpTy GATE (MODULE xs) -> Void
gateMod (PP _) impossible
gateMod UU impossible
gateMod (MM _) impossible
gateMod (CM _) impossible
gateMod DD impossible
gateMod CC impossible
gateMod GG impossible

gateUni : InterpTy GATE UNIT -> Void
gateUni (PP _) impossible
gateUni UU impossible
gateUni (MM _) impossible
gateUni (CM _) impossible
gateUni DD impossible
gateUni CC impossible
gateUni GG impossible

gatePor : InterpTy GATE (PORT x) -> Void
gatePor (PP _) impossible
gatePor UU impossible
gatePor (MM _) impossible
gatePor (CM _) impossible
gatePor DD impossible
gatePor CC impossible
gatePor GG impossible

gateTyp : InterpTy GATE TYPE -> Void
gateTyp (PP _) impossible
gateTyp UU impossible
gateTyp (MM _) impossible
gateTyp (CM _) impossible
gateTyp DD impossible
gateTyp CC impossible
gateTyp GG impossible

gateDat : InterpTy GATE DATA -> Void
gateDat (PP _) impossible
gateDat UU impossible
gateDat (MM _) impossible
gateDat (CM _) impossible
gateDat DD impossible
gateDat CC impossible
gateDat GG impossible

gateMIn : InterpTy GATE (MINST xs) -> Void
gateMIn (PP _) impossible
gateMIn UU impossible
gateMIn (MM _) impossible
gateMIn (CM _) impossible
gateMIn DD impossible
gateMIn CC impossible
gateMIn GG impossible

gateGat : InterpTy GATE GATE -> Void
gateGat (PP _) impossible
gateGat UU impossible
gateGat (MM _) impossible
gateGat (CM _) impossible
gateGat DD impossible
gateGat CC impossible
gateGat GG impossible

gateChan : InterpTy GATE CHAN -> Void
gateChan (PP _) impossible
gateChan UU impossible
gateChan (MM _) impossible
gateChan (CM _) impossible
gateChan DD impossible
gateChan CC impossible
gateChan GG impossible

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
interpTy PORT GATE = No portGat
interpTy PORT GINST = No portGinst

interpTy UNIT (MODULE xs) = No unitMod
interpTy UNIT DATA = No unitDat
interpTy UNIT CHAN = No unitCh
interpTy UNIT (PORT x) = No unitPor
interpTy UNIT (MINST xs) = No unitMIn
interpTy UNIT UNIT = Yes UU
interpTy UNIT TYPE = No unitTyp
interpTy UNIT GATE = No unitGat
interpTy UNIT GINST = No unitGinst

interpTy MODULE (MODULE xs) = Yes (MM xs)
interpTy MODULE DATA = No moduleDat
interpTy MODULE CHAN = No moduleCh
interpTy MODULE (PORT x) = No modulePor
interpTy MODULE (MINST xs) = No moduleMIn
interpTy MODULE UNIT = No moduleUni
interpTy MODULE TYPE = No moduleTyp
interpTy MODULE GATE = No moduleGat
interpTy MODULE GINST = No moduleGinst

interpTy CONN (MODULE xs) = No connMod
interpTy CONN DATA = No connDat
interpTy CONN CHAN = No connCh
interpTy CONN (PORT x) = No connPor
interpTy CONN (MINST xs) = Yes (CM xs)
interpTy CONN UNIT = No connUni
interpTy CONN TYPE = No connTyp
interpTy CONN GATE = No connGat
interpTy CONN GINST = No connGinst

interpTy DATA (MODULE xs) = No dataMod
interpTy DATA DATA = Yes DD
interpTy DATA CHAN = No dataCh
interpTy DATA (PORT x) = No dataPor
interpTy DATA (MINST xs) = No dataMIn
interpTy DATA UNIT = No dataUni
interpTy DATA TYPE = No dataTyp
interpTy DATA GATE = No dataGat
interpTy DATA GINST = No dataGinst

interpTy CHAN (MODULE xs) = No chanMod
interpTy CHAN DATA = No chanDat
interpTy CHAN CHAN = Yes CC
interpTy CHAN (PORT x) = No chanPor
interpTy CHAN (MINST xs) = No chanMIn
interpTy CHAN UNIT = No chanUni
interpTy CHAN TYPE = No chanTyp
interpTy CHAN GATE = No chanGat
interpTy CHAN GINST = No chanGinst

interpTy GATE (MODULE xs) = No gateMod
interpTy GATE DATA        = No gateDat
interpTy GATE CHAN        = No gateChan
interpTy GATE (PORT x)    = No gatePor
interpTy GATE (MINST xs)  = No gateMIn
interpTy GATE UNIT        = No gateUni
interpTy GATE TYPE        = No gateTyp
interpTy GATE GATE        = No gateGat
interpTy GATE GINST       = Yes GG

namespace TyIR
  public export
  data IsGlobal : TyIR -> Type where
    IsDeclM : IsGlobal MODULE
    IsDeclD : IsGlobal DATA

  public export
  data IsLocal : TyIR -> Type where
    IsInstM : IsLocal CONN
    IsInstC : IsLocal CHAN
    IsInstG : IsLocal GATE

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
  isBindable GATE = IsLet IsInstG

-- --------------------------------------------------------------------- [ EOF ]
