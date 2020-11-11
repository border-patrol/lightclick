module Language.SystemVerilog.MetaTypes

import        Data.Strings

import public Toolkit.Data.DList.DeBruijn
import public Toolkit.Decidable.Equality.Indexed

%default total

public export
data Ty = MODULE (List String)
        | DATA
        | CHAN
        | PORT String
        | MINST (List String)
        | UNIT
        | TYPE
        | GATE
        | GINST

export
Show Ty where
  show (MODULE xs) = unwords ["(MODULE", show xs, ")"]
  show DATA = "(DATA)"
  show CHAN = "(CHAN)"
  show (PORT x) = unwords ["(PORT", show x, ")"]
  show (MINST xs) = unwords ["(MINST", show xs, ")"]
  show UNIT = "(UNIT)"
  show TYPE = "(TYPE)"
  show GATE = "(GATE)"
  show GINST = "(GINST)"

public export
Context : Type
Context = List (Pair String Ty)

public export
Index : Context -> Pair String Ty -> Type
Index = DeBruijn.Index (Pair String Ty)

export
Eq Ty where
  (==) (MODULE xs)   (MODULE ys)     = xs == ys
  (==) DATA          DATA            = True
  (==) CHAN          CHAN            = True
  (==) (PORT x)      (PORT y)        = x == y
  (==) (MINST xs)    (MINST ys)      = xs == ys
  (==) UNIT          UNIT            = True
  (==) TYPE          TYPE            = True
  (==) GATE          GATE            = True
  (==) GINST         GINST           = True
  (==) _             _               = False


namespace DecEq

  -- Modules

  modulesDifferentNames : (xs : List String)
                       -> (ys : List String)
                       -> (contra : (xs = ys) -> Void)
                       -> (MODULE xs = MODULE ys)
                       -> Void
  modulesDifferentNames ys ys contra Refl = contra Refl

  moduleDataNotEq : (MODULE xs = DATA) -> Void
  moduleDataNotEq Refl impossible

  moduleChanNotEq : (MODULE xs = CHAN) -> Void
  moduleChanNotEq Refl impossible

  modulePortNotEq : (MODULE xs = PORT x) -> Void
  modulePortNotEq Refl impossible

  moduleDeclmoduleInstNotEq : (MODULE xs = MINST ys) -> Void
  moduleDeclmoduleInstNotEq Refl impossible

  moduleUnitNotEq : (MODULE xs = UNIT) -> Void
  moduleUnitNotEq Refl impossible

  moduleTypeNotEq : (MODULE xs = TYPE) -> Void
  moduleTypeNotEq Refl impossible

  moduleGateNotEq : (MODULE xs = GATE) -> Void
  moduleGateNotEq Refl impossible

  moduleGinstNotEq : (MODULE xs = GINST) -> Void
  moduleGinstNotEq Refl impossible

  -- Data.

  dataChanNotEq : (DATA = CHAN) -> Void
  dataChanNotEq Refl impossible

  dataPortNotEq : (DATA = PORT x) -> Void
  dataPortNotEq Refl impossible

  dataModuleInstNotEq : (DATA = MINST xs) -> Void
  dataModuleInstNotEq Refl impossible

  dataUnitNotEq : (DATA = UNIT) -> Void
  dataUnitNotEq Refl impossible

  dataTypeNotEq : (DATA = TYPE) -> Void
  dataTypeNotEq Refl impossible

  dataGateNotEq : (DATA = GATE) -> Void
  dataGateNotEq Refl impossible

  dataGinstNotEq : (DATA = GINST) -> Void
  dataGinstNotEq Refl impossible

  -- Channels

  chanPortNotEq : (CHAN = PORT x) -> Void
  chanPortNotEq Refl impossible

  chanModuleInstNotEq : (CHAN = MINST xs) -> Void
  chanModuleInstNotEq Refl impossible

  chanUnitNotEq : (CHAN = UNIT) -> Void
  chanUnitNotEq Refl impossible

  chanTypeNotEq : (CHAN = TYPE) -> Void
  chanTypeNotEq Refl impossible

  chanGateNotEq : (CHAN = GATE) -> Void
  chanGateNotEq Refl impossible

  chanGinstNotEq : (CHAN = GINST) -> Void
  chanGinstNotEq Refl impossible



  -- Port

  portLabelMismatch : (contra : (x = y) -> Void) -> (PORT x = PORT y) -> Void
  portLabelMismatch contra Refl = contra Refl

  portModuleInstNotEq : (PORT x = MINST xs) -> Void
  portModuleInstNotEq Refl impossible

  portUnitNotEq : (PORT x = UNIT) -> Void
  portUnitNotEq Refl impossible

  portTypeNotEq : (PORT x = TYPE) -> Void
  portTypeNotEq Refl impossible

  portGateNotEq : (PORT x = GATE) -> Void
  portGateNotEq Refl impossible

  portGinstNotEq : (PORT x = GINST) -> Void
  portGinstNotEq Refl impossible

  -- MInst
  moduleInstParamsDiffer : (xs : List String)
                        -> (ys : List String)
                        -> (contra : (xs = ys) -> Void) -> (MINST xs = MINST ys) -> Void
  moduleInstParamsDiffer ys ys contra Refl = contra Refl

  moduleInstUnitNotEq : (MINST xs = UNIT) -> Void
  moduleInstUnitNotEq Refl impossible

  moduleInstTypeNotEq : (MINST xs = TYPE) -> Void
  moduleInstTypeNotEq Refl impossible

  moduleInstGateNotEq : (MINST xs = GATE) -> Void
  moduleInstGateNotEq Refl impossible

  moduleInstGinstNotEq : (MINST xs = GINST) -> Void
  moduleInstGinstNotEq Refl impossible

  -- Unit

  unitTypeNotEq : (UNIT = TYPE) -> Void
  unitTypeNotEq Refl impossible

  unitGateNotEq : (UNIT = GATE) -> Void
  unitGateNotEq Refl impossible

  unitGinstNotEq : (UNIT = GINST) -> Void
  unitGinstNotEq Refl impossible

  -- Type

  typeGateNotEq : (TYPE = GATE) -> Void
  typeGateNotEq Refl impossible

  typeGinstNotEq : (TYPE = GINST) -> Void
  typeGinstNotEq Refl impossible

  -- Gate
  gateGinstNotEq : (GATE = GINST) -> Void
  gateGinstNotEq Refl impossible

  -- Definition

  decEqTy : (x,y : Ty) -> Dec (x = y)
  decEqTy (MODULE xs) ty with (ty)
    decEqTy (MODULE xs) ty | (MODULE ys) with (decEq xs ys)
      decEqTy (MODULE ys) ty | (MODULE ys) | (Yes Refl) = Yes Refl
      decEqTy (MODULE xs) ty | (MODULE ys) | (No contra) = No (modulesDifferentNames xs ys contra)

    decEqTy (MODULE xs) ty | DATA = No (moduleDataNotEq)
    decEqTy (MODULE xs) ty | CHAN = No (moduleChanNotEq)
    decEqTy (MODULE xs) ty | (PORT x) = No (modulePortNotEq)
    decEqTy (MODULE xs) ty | (MINST ys) = No (moduleDeclmoduleInstNotEq)
    decEqTy (MODULE xs) ty | UNIT = No (moduleUnitNotEq)
    decEqTy (MODULE xs) ty | TYPE = No (moduleTypeNotEq)
    decEqTy (MODULE xs) ty | GATE = No (moduleGateNotEq)
    decEqTy (MODULE xs) ty | (GINST) = No (moduleGinstNotEq)

  decEqTy DATA ty with (ty)
    decEqTy DATA ty | (MODULE xs) = No (negEqSym moduleDataNotEq)
    decEqTy DATA ty | DATA = Yes Refl
    decEqTy DATA ty | CHAN = No (dataChanNotEq)
    decEqTy DATA ty | (PORT x) = No (dataPortNotEq)
    decEqTy DATA ty | (MINST xs) = No (dataModuleInstNotEq)
    decEqTy DATA ty | UNIT = No (dataUnitNotEq)
    decEqTy DATA ty | TYPE = No (dataTypeNotEq)
    decEqTy DATA ty | GATE = No (dataGateNotEq)
    decEqTy DATA ty | (GINST) = No (dataGinstNotEq)

  decEqTy CHAN ty with (ty)
    decEqTy CHAN ty | (MODULE xs) = No (negEqSym moduleChanNotEq)
    decEqTy CHAN ty | DATA = No (negEqSym dataChanNotEq)
    decEqTy CHAN ty | CHAN = Yes Refl
    decEqTy CHAN ty | (PORT x) = No (chanPortNotEq)
    decEqTy CHAN ty | (MINST xs) = No (chanModuleInstNotEq)
    decEqTy CHAN ty | UNIT = No (chanUnitNotEq)
    decEqTy CHAN ty | TYPE = No (chanTypeNotEq)
    decEqTy CHAN ty | GATE = No (chanGateNotEq)
    decEqTy CHAN ty | (GINST) = No (chanGinstNotEq)

  decEqTy (PORT x) ty with (ty)
    decEqTy (PORT x) ty | (MODULE xs) = No (negEqSym modulePortNotEq)
    decEqTy (PORT x) ty | DATA = No (negEqSym dataPortNotEq)
    decEqTy (PORT x) ty | CHAN = No (negEqSym chanPortNotEq)
    decEqTy (PORT x) ty | (PORT y) with (decEq x y)
      decEqTy (PORT y) ty | (PORT y) | (Yes Refl) = Yes Refl
      decEqTy (PORT x) ty | (PORT y) | (No contra) = No (portLabelMismatch contra)

    decEqTy (PORT x) ty | (MINST xs) = No (portModuleInstNotEq)
    decEqTy (PORT x) ty | UNIT = No (portUnitNotEq)
    decEqTy (PORT x) ty | TYPE = No (portTypeNotEq)
    decEqTy (PORT x) ty | GATE = No (portGateNotEq)
    decEqTy (PORT x) ty | (GINST) = No (portGinstNotEq)

  decEqTy (MINST xs) ty with (ty)
    decEqTy (MINST xs) ty | (MODULE ys) = No (negEqSym moduleDeclmoduleInstNotEq)
    decEqTy (MINST xs) ty | DATA = No (negEqSym dataModuleInstNotEq)
    decEqTy (MINST xs) ty | CHAN = No (negEqSym chanModuleInstNotEq)
    decEqTy (MINST xs) ty | (PORT x) = No (negEqSym portModuleInstNotEq)
    decEqTy (MINST xs) ty | (MINST ys) with (decEq xs ys)
      decEqTy (MINST ys) ty | (MINST ys) | (Yes Refl) = Yes Refl
      decEqTy (MINST xs) ty | (MINST ys) | (No contra) = No (moduleInstParamsDiffer xs ys contra)

    decEqTy (MINST xs) ty | UNIT = No moduleInstUnitNotEq
    decEqTy (MINST xs) ty | TYPE = No moduleInstTypeNotEq
    decEqTy (MINST xs) ty | GATE = No moduleInstGateNotEq
    decEqTy (MINST xs) ty | (GINST) = No moduleInstGinstNotEq


  decEqTy UNIT ty with (ty)
    decEqTy UNIT ty | (MODULE xs) = No (negEqSym moduleUnitNotEq)
    decEqTy UNIT ty | DATA = No (negEqSym dataUnitNotEq)
    decEqTy UNIT ty | CHAN = No (negEqSym chanUnitNotEq)
    decEqTy UNIT ty | (PORT x) = No (negEqSym portUnitNotEq)
    decEqTy UNIT ty | (MINST xs) = No (negEqSym moduleInstUnitNotEq)
    decEqTy UNIT ty | UNIT = Yes Refl
    decEqTy UNIT ty | TYPE = No unitTypeNotEq
    decEqTy UNIT ty | GATE = No unitGateNotEq
    decEqTy UNIT ty | (GINST) = No unitGinstNotEq

  decEqTy TYPE ty with (ty)
    decEqTy TYPE ty | (MODULE xs) = No (negEqSym moduleTypeNotEq)
    decEqTy TYPE ty | DATA = No (negEqSym dataTypeNotEq)
    decEqTy TYPE ty | CHAN = No (negEqSym chanTypeNotEq)
    decEqTy TYPE ty | (PORT x) = No (negEqSym portTypeNotEq)
    decEqTy TYPE ty | (MINST xs) = No (negEqSym moduleInstTypeNotEq)
    decEqTy TYPE ty | UNIT = No (negEqSym unitTypeNotEq)
    decEqTy TYPE ty | TYPE = Yes Refl
    decEqTy TYPE ty | GATE = No typeGateNotEq
    decEqTy TYPE ty | (GINST) = No typeGinstNotEq

  decEqTy GATE ty with (ty)
    decEqTy GATE ty | (MODULE xs) = No (negEqSym moduleGateNotEq)
    decEqTy GATE ty | DATA = No (negEqSym dataGateNotEq)
    decEqTy GATE ty | CHAN = No (negEqSym chanGateNotEq)
    decEqTy GATE ty | (PORT x) = No (negEqSym portGateNotEq)
    decEqTy GATE ty | (MINST xs) = No (negEqSym moduleInstGateNotEq)
    decEqTy GATE ty | UNIT = No (negEqSym unitGateNotEq)
    decEqTy GATE ty | TYPE = No (negEqSym typeGateNotEq)
    decEqTy GATE ty | GATE = Yes Refl
    decEqTy GATE ty | (GINST) = No gateGinstNotEq

  decEqTy (GINST) ty with (ty)
    decEqTy (GINST) ty | (MODULE xs) = No (negEqSym moduleGinstNotEq)
    decEqTy (GINST) ty | DATA = No (negEqSym dataGinstNotEq)
    decEqTy (GINST) ty | CHAN = No (negEqSym chanGinstNotEq)
    decEqTy (GINST) ty | (PORT x) = No (negEqSym portGinstNotEq)
    decEqTy (GINST) ty | (MINST xs) = No (negEqSym moduleInstGinstNotEq)
    decEqTy (GINST) ty | UNIT = No (negEqSym unitGinstNotEq)
    decEqTy (GINST) ty | TYPE = No (negEqSym typeGinstNotEq)
    decEqTy (GINST) ty | GATE = No (negEqSym gateGinstNotEq)
    decEqTy (GINST) ty | (GINST) = Yes Refl

  export
  DecEq Ty where
   decEq = decEqTy

namespace Validity

  namespace Decl
    public export
    data ValidDecl : (expr : Ty) -> (type : Ty) -> Type where
       IsDeclM : ValidDecl (MODULE names) TYPE
       IsDeclD : ValidDecl DATA           TYPE


    -- Modules

    moduleCannotHaveTypeModule : ValidDecl (MODULE xs) (MODULE ys) -> Void
    moduleCannotHaveTypeModule IsDeclM impossible
    moduleCannotHaveTypeModule IsDeclD impossible

    moduleCannotHaveTypeData : ValidDecl (MODULE xs) DATA -> Void
    moduleCannotHaveTypeData IsDeclM impossible
    moduleCannotHaveTypeData IsDeclD impossible

    moduleCannotHaveTypeChan : ValidDecl (MODULE xs) CHAN -> Void
    moduleCannotHaveTypeChan IsDeclM impossible
    moduleCannotHaveTypeChan IsDeclD impossible

    moduleCannotHaveTypePort : ValidDecl (MODULE xs) (PORT x) -> Void
    moduleCannotHaveTypePort IsDeclM impossible
    moduleCannotHaveTypePort IsDeclD impossible

    moduleCannotHaveTypeMInst : ValidDecl (MODULE xs) (MINST ys) -> Void
    moduleCannotHaveTypeMInst IsDeclM impossible
    moduleCannotHaveTypeMInst IsDeclD impossible

    moduleCannotHaveTypeUnit : ValidDecl (MODULE xs) UNIT -> Void
    moduleCannotHaveTypeUnit IsDeclM impossible
    moduleCannotHaveTypeUnit IsDeclD impossible

    moduleCannotHaveTypeGate : ValidDecl (MODULE xs) GATE -> Void
    moduleCannotHaveTypeGate IsDeclM impossible
    moduleCannotHaveTypeGate IsDeclD impossible

    moduleCannotHaveTypeGinst : ValidDecl (MODULE xs) (GINST) -> Void
    moduleCannotHaveTypeGinst IsDeclM impossible
    moduleCannotHaveTypeGinst IsDeclD impossible


    -- Data

    dataCannotHaveTypeModule : ValidDecl DATA (MODULE xs) -> Void
    dataCannotHaveTypeModule IsDeclM impossible
    dataCannotHaveTypeModule IsDeclD impossible

    dataCannotHaveTypeData : ValidDecl DATA DATA -> Void
    dataCannotHaveTypeData IsDeclM impossible
    dataCannotHaveTypeData IsDeclD impossible

    dataCannotHaveTypeChan : ValidDecl DATA CHAN -> Void
    dataCannotHaveTypeChan IsDeclM impossible
    dataCannotHaveTypeChan IsDeclD impossible

    dataCannotHaveTypePort : ValidDecl DATA (PORT x) -> Void
    dataCannotHaveTypePort IsDeclM impossible
    dataCannotHaveTypePort IsDeclD impossible

    dataCannotHaveTypeMInst : ValidDecl DATA (MINST xs) -> Void
    dataCannotHaveTypeMInst IsDeclM impossible
    dataCannotHaveTypeMInst IsDeclD impossible

    dataCannotHaveTypeUnit : ValidDecl DATA UNIT -> Void
    dataCannotHaveTypeUnit IsDeclM impossible
    dataCannotHaveTypeUnit IsDeclD impossible

    dataCannotHaveTypeGate : ValidDecl DATA GATE -> Void
    dataCannotHaveTypeGate IsDeclM impossible
    dataCannotHaveTypeGate IsDeclD impossible

    dataCannotHaveTypeGinst : ValidDecl DATA (GINST) -> Void
    dataCannotHaveTypeGinst IsDeclM impossible
    dataCannotHaveTypeGinst IsDeclD impossible

    -- CHAN

    chanCannotBeDecl : ValidDecl CHAN type -> Void
    chanCannotBeDecl IsDeclM impossible
    chanCannotBeDecl IsDeclD impossible

    portCannotBeDecl : ValidDecl (PORT x) type -> Void
    portCannotBeDecl IsDeclM impossible
    portCannotBeDecl IsDeclD impossible

    minstsCannotBeDecl : ValidDecl (MINST xs) type -> Void
    minstsCannotBeDecl IsDeclM impossible
    minstsCannotBeDecl IsDeclD impossible

    unitCannotBeDecl : ValidDecl UNIT type -> Void
    unitCannotBeDecl IsDeclM impossible
    unitCannotBeDecl IsDeclD impossible

    typeCannotBeDecl : ValidDecl TYPE type -> Void
    typeCannotBeDecl IsDeclM impossible
    typeCannotBeDecl IsDeclD impossible

    gateCannotBeDecl : ValidDecl GATE type -> Void
    gateCannotBeDecl IsDeclM impossible
    gateCannotBeDecl IsDeclD impossible

    ginstCannotBeDecl : ValidDecl (GINST) type -> Void
    ginstCannotBeDecl IsDeclM impossible
    ginstCannotBeDecl IsDeclD impossible

    export
    validDecl : (expr : Ty)
             -> (type : Ty)
             -> Dec (ValidDecl expr type)
    validDecl (MODULE xs) (MODULE ys) = No moduleCannotHaveTypeModule
    validDecl (MODULE xs) DATA = No moduleCannotHaveTypeData
    validDecl (MODULE xs) CHAN = No moduleCannotHaveTypeChan
    validDecl (MODULE xs) (PORT x) = No moduleCannotHaveTypePort
    validDecl (MODULE xs) (MINST ys) = No moduleCannotHaveTypeMInst
    validDecl (MODULE xs) UNIT = No moduleCannotHaveTypeUnit
    validDecl (MODULE xs) TYPE = Yes IsDeclM
    validDecl (MODULE xs) GATE = No moduleCannotHaveTypeGate
    validDecl (MODULE xs) (GINST) = No moduleCannotHaveTypeGinst

    validDecl DATA (MODULE xs) = No dataCannotHaveTypeModule
    validDecl DATA DATA = No dataCannotHaveTypeData
    validDecl DATA CHAN = No dataCannotHaveTypeChan
    validDecl DATA (PORT x) = No dataCannotHaveTypePort
    validDecl DATA (MINST xs) = No dataCannotHaveTypeMInst
    validDecl DATA UNIT = No dataCannotHaveTypeUnit
    validDecl DATA TYPE = Yes IsDeclD
    validDecl DATA GATE = No dataCannotHaveTypeGate
    validDecl DATA (GINST) = No dataCannotHaveTypeGinst

    validDecl CHAN _ = No chanCannotBeDecl
    validDecl (PORT x) _ = No portCannotBeDecl
    validDecl (MINST xs) _ = No minstsCannotBeDecl
    validDecl UNIT _ = No unitCannotBeDecl
    validDecl TYPE _ = No typeCannotBeDecl
    validDecl GATE _ = No gateCannotBeDecl
    validDecl (GINST) _ = No ginstCannotBeDecl

  namespace LetBinding
    public export
    data ValidLet : (expr : Ty) -> (type : Ty) -> Type where
       IsLetMM : (prf :                 xs  =         ys)
                     -> ValidLet (MINST xs)   (MODULE ys)

       IsLetCD : ValidLet CHAN DATA

       IsLetGG : ValidLet (GINST) GATE

       IsLetDecl : ValidDecl expr ty
                -> ValidLet  expr ty

    -- Modules

    moduleCannotHaveTypeModuleLocal : ValidLet (MODULE xs) (MODULE ys) -> Void
    moduleCannotHaveTypeModuleLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeModuleLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeDataLocal : ValidLet (MODULE xs) DATA -> Void
    moduleCannotHaveTypeDataLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeDataLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeChanLocal :  ValidLet (MODULE xs) CHAN -> Void
    moduleCannotHaveTypeChanLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeChanLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypePortLocal : ValidLet (MODULE xs) (PORT y) -> Void
    moduleCannotHaveTypePortLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypePortLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeMInstLocal : ValidLet (MODULE xs) (MINST ys) -> Void
    moduleCannotHaveTypeMInstLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeMInstLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeUnitLocal : ValidLet (MODULE xs) UNIT -> Void
    moduleCannotHaveTypeUnitLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeUnitLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeGateLocal : ValidLet (MODULE xs) GATE -> Void
    moduleCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    moduleCannotHaveTypeGInstLocal : ValidLet (MODULE xs) (GINST) -> Void
    moduleCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    moduleCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Data

    dataCannotHaveTypeModuleLocal : ValidLet DATA (MODULE xs) -> Void
    dataCannotHaveTypeModuleLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeModuleLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeDataLocal : ValidLet DATA DATA -> Void
    dataCannotHaveTypeDataLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeDataLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeChanLocal : ValidLet DATA CHAN -> Void
    dataCannotHaveTypeChanLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeChanLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypePortLocal : ValidLet DATA (PORT y) -> Void
    dataCannotHaveTypePortLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypePortLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeMInstLocal : ValidLet DATA (MINST xs) -> Void
    dataCannotHaveTypeMInstLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeMInstLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeUnitLocal : ValidLet DATA UNIT -> Void
    dataCannotHaveTypeUnitLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeUnitLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeGateLocal : ValidLet DATA GATE -> Void
    dataCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    dataCannotHaveTypeGInstLocal : ValidLet DATA (GINST) -> Void
    dataCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    dataCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Chan

    chanCannotHaveTypeType : ValidLet CHAN TYPE -> Void
    chanCannotHaveTypeType (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeType (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeModule : ValidLet CHAN (MODULE xs) -> Void
    chanCannotHaveTypeModule (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeModule (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeChan : ValidLet CHAN CHAN -> Void
    chanCannotHaveTypeChan (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeChan (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypePort : ValidLet CHAN (PORT y) -> Void
    chanCannotHaveTypePort (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypePort (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeMInst : ValidLet CHAN (MINST xs) -> Void
    chanCannotHaveTypeMInst (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeMInst (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeUnit : ValidLet CHAN UNIT -> Void
    chanCannotHaveTypeUnit (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeUnit (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeGateLocal : ValidLet CHAN GATE -> Void
    chanCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    chanCannotHaveTypeGInstLocal : ValidLet CHAN (GINST) -> Void
    chanCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    chanCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Ports

    portCannotHaveTypeModule : ValidLet (PORT y) (MODULE xs) -> Void
    portCannotHaveTypeModule (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeModule (IsLetDecl IsDeclD) impossible

    portCannotHaveTypeData : ValidLet (PORT y) DATA -> Void
    portCannotHaveTypeData (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeData (IsLetDecl IsDeclD) impossible


    portCannotHaveTypeChan : ValidLet (PORT y) CHAN -> Void
    portCannotHaveTypeChan (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeChan (IsLetDecl IsDeclD) impossible

    portCannotHaveTypePort : ValidLet (PORT y) (PORT x) -> Void
    portCannotHaveTypePort (IsLetDecl IsDeclM) impossible
    portCannotHaveTypePort (IsLetDecl IsDeclD) impossible

    portCannotHaveTypeMInst : ValidLet (PORT y) (MINST xs) -> Void
    portCannotHaveTypeMInst (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeMInst (IsLetDecl IsDeclD) impossible

    portCannotHaveTypeUnit : ValidLet (PORT y) UNIT -> Void
    portCannotHaveTypeUnit (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeUnit(IsLetDecl IsDeclD) impossible

    portCannotHaveTypeType : ValidLet (PORT y) TYPE -> Void
    portCannotHaveTypeType (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeType (IsLetDecl IsDeclD) impossible

    portCannotHaveTypeGateLocal : ValidLet (PORT p) GATE -> Void
    portCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    portCannotHaveTypeGInstLocal : ValidLet (PORT p) (GINST) -> Void
    portCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    portCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- MINST

    minstCannotHaveTypeData : ValidLet (MINST xs) DATA -> Void
    minstCannotHaveTypeData (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeData (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeChan : ValidLet (MINST xs) CHAN -> Void
    minstCannotHaveTypeChan (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeChan (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypePort : ValidLet (MINST xs) (PORT x) -> Void
    minstCannotHaveTypePort (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypePort (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeMInst : ValidLet (MINST xs) (MINST ys) -> Void
    minstCannotHaveTypeMInst (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeMInst (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeUnit : ValidLet (MINST xs) UNIT -> Void
    minstCannotHaveTypeUnit (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeUnit(IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeType : ValidLet (MINST xs) TYPE -> Void
    minstCannotHaveTypeType (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeType (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeGateLocal : ValidLet (MINST xs) GATE -> Void
    minstCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    minstCannotHaveTypeGInstLocal : ValidLet (MINST xs) (GINST) -> Void
    minstCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    minstCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Unit
    unitCannotHaveTypeModule : ValidLet UNIT (MODULE xs) -> Void
    unitCannotHaveTypeModule (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeModule (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeData : ValidLet UNIT DATA -> Void
    unitCannotHaveTypeData (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeData (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeChan : ValidLet UNIT CHAN -> Void
    unitCannotHaveTypeChan (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeChan (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypePort : ValidLet UNIT (PORT x) -> Void
    unitCannotHaveTypePort (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypePort (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeMInst : ValidLet UNIT (MINST xs) -> Void
    unitCannotHaveTypeMInst (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeMInst (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeUnit : ValidLet UNIT UNIT -> Void
    unitCannotHaveTypeUnit (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeUnit(IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeType : ValidLet UNIT TYPE -> Void
    unitCannotHaveTypeType (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeType (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeGateLocal : ValidLet UNIT GATE -> Void
    unitCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    unitCannotHaveTypeGInstLocal : ValidLet UNIT (GINST) -> Void
    unitCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    unitCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- TYPE

    typeCannotHaveTypeModule : ValidLet TYPE (MODULE xs) -> Void
    typeCannotHaveTypeModule (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeModule (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeData : ValidLet TYPE DATA -> Void
    typeCannotHaveTypeData (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeData (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeChan : ValidLet TYPE CHAN -> Void
    typeCannotHaveTypeChan (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeChan (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypePort : ValidLet TYPE (PORT x) -> Void
    typeCannotHaveTypePort (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypePort (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeMInst : ValidLet TYPE (MINST xs) -> Void
    typeCannotHaveTypeMInst (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeMInst (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeUnit : ValidLet TYPE UNIT -> Void
    typeCannotHaveTypeUnit (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeUnit(IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeType : ValidLet TYPE TYPE -> Void
    typeCannotHaveTypeType (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeType (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeGateLocal : ValidLet TYPE GATE -> Void
    typeCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    typeCannotHaveTypeGInstLocal : ValidLet TYPE (GINST) -> Void
    typeCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    typeCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Gates

    gateCannotHaveTypeModuleLocal : ValidLet GATE (MODULE xs) -> Void
    gateCannotHaveTypeModuleLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeModuleLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeDataLocal : ValidLet GATE DATA -> Void
    gateCannotHaveTypeDataLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeDataLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeChanLocal : ValidLet GATE CHAN -> Void
    gateCannotHaveTypeChanLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeChanLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypePortLocal : ValidLet GATE (PORT y) -> Void
    gateCannotHaveTypePortLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypePortLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeMInstLocal : ValidLet GATE (MINST xs) -> Void
    gateCannotHaveTypeMInstLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeMInstLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeUnitLocal : ValidLet GATE UNIT -> Void
    gateCannotHaveTypeUnitLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeUnitLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeGateLocal : ValidLet GATE GATE -> Void
    gateCannotHaveTypeGateLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeGateLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeGInstLocal : ValidLet GATE (GINST) -> Void
    gateCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    gateCannotHaveTypeTypeLocal : ValidLet GATE TYPE -> Void
    gateCannotHaveTypeTypeLocal (IsLetDecl IsDeclM) impossible
    gateCannotHaveTypeTypeLocal (IsLetDecl IsDeclD) impossible

    -- GInst

    ginstCannotHaveTypeModuleLocal : ValidLet (GINST) (MODULE xs) -> Void
    ginstCannotHaveTypeModuleLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeModuleLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeDataLocal : ValidLet (GINST) DATA -> Void
    ginstCannotHaveTypeDataLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeDataLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeChanLocal : ValidLet (GINST) CHAN -> Void
    ginstCannotHaveTypeChanLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeChanLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypePortLocal : ValidLet (GINST) (PORT y) -> Void
    ginstCannotHaveTypePortLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypePortLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeMInstLocal : ValidLet (GINST) (MINST xs) -> Void
    ginstCannotHaveTypeMInstLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeMInstLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeUnitLocal : ValidLet (GINST) UNIT -> Void
    ginstCannotHaveTypeUnitLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeUnitLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeTypeLocal : ValidLet (GINST) TYPE -> Void
    ginstCannotHaveTypeTypeLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeTypeLocal (IsLetDecl IsDeclD) impossible

    ginstCannotHaveTypeGInstLocal : ValidLet (GINST) (GINST) -> Void
    ginstCannotHaveTypeGInstLocal (IsLetDecl IsDeclM) impossible
    ginstCannotHaveTypeGInstLocal (IsLetDecl IsDeclD) impossible

    -- Misc
    minstAndModulesHaveDiffNames : (f : (xs = ys) -> Void)
                                -> ValidLet (MINST xs) (MODULE ys)
                                -> Void
    minstAndModulesHaveDiffNames f (IsLetMM Refl) = f Refl
    minstAndModulesHaveDiffNames _ (IsLetDecl IsDeclM) impossible
    minstAndModulesHaveDiffNames _ (IsLetDecl IsDeclD) impossible

    export
    validLet : (expr : Ty)
            -> (type : Ty)
            -> Dec (ValidLet expr type)
    validLet (MODULE xs) (MODULE ys) = No moduleCannotHaveTypeModuleLocal
    validLet (MODULE xs) DATA        = No moduleCannotHaveTypeDataLocal
    validLet (MODULE xs) CHAN        = No moduleCannotHaveTypeChanLocal
    validLet (MODULE xs) (PORT x)    = No moduleCannotHaveTypePortLocal
    validLet (MODULE xs) (MINST ys)  = No moduleCannotHaveTypeMInstLocal
    validLet (MODULE xs) UNIT        = No moduleCannotHaveTypeUnitLocal
    validLet (MODULE xs) TYPE        = Yes (IsLetDecl IsDeclM)
    validLet (MODULE xs) GATE        = No moduleCannotHaveTypeGateLocal
    validLet (MODULE xs) (GINST) = No moduleCannotHaveTypeGInstLocal

    validLet DATA (MODULE xs) = No (dataCannotHaveTypeModuleLocal)
    validLet DATA DATA        = No (dataCannotHaveTypeDataLocal)
    validLet DATA CHAN        = No (dataCannotHaveTypeChanLocal)
    validLet DATA (PORT x)    = No (dataCannotHaveTypePortLocal)
    validLet DATA (MINST xs)  = No (dataCannotHaveTypeMInstLocal)
    validLet DATA UNIT        = No (dataCannotHaveTypeUnitLocal)
    validLet DATA TYPE        = Yes (IsLetDecl IsDeclD)
    validLet DATA GATE         = No dataCannotHaveTypeGateLocal
    validLet DATA (GINST) = No dataCannotHaveTypeGInstLocal

    validLet CHAN (MODULE xs) = No (chanCannotHaveTypeModule)
    validLet CHAN DATA        = Yes IsLetCD
    validLet CHAN CHAN        = No (chanCannotHaveTypeChan)
    validLet CHAN (PORT x)    = No (chanCannotHaveTypePort)
    validLet CHAN (MINST xs)  = No (chanCannotHaveTypeMInst)
    validLet CHAN UNIT        = No (chanCannotHaveTypeUnit)
    validLet CHAN TYPE        = No (chanCannotHaveTypeType)
    validLet CHAN GATE         = No chanCannotHaveTypeGateLocal
    validLet CHAN (GINST) = No chanCannotHaveTypeGInstLocal

    validLet (PORT x) (MODULE xs) =  No portCannotHaveTypeModule
    validLet (PORT x) DATA        =  No portCannotHaveTypeData
    validLet (PORT x) CHAN        =  No (portCannotHaveTypeChan)
    validLet (PORT x) (PORT y)    =  No portCannotHaveTypePort
    validLet (PORT x) (MINST xs)  =  No portCannotHaveTypeMInst
    validLet (PORT x) UNIT        =  No portCannotHaveTypeUnit
    validLet (PORT x) TYPE        =  No portCannotHaveTypeType
    validLet (PORT x) GATE         = No portCannotHaveTypeGateLocal
    validLet (PORT x) (GINST) = No portCannotHaveTypeGInstLocal


    validLet (MINST xs) (MODULE ys) with (decEq xs ys)
      validLet (MINST ys) (MODULE ys) | (Yes Refl) = Yes (IsLetMM Refl)
      validLet (MINST xs) (MODULE ys) | (No contra) = No (minstAndModulesHaveDiffNames contra)

    validLet (MINST xs) DATA       =  No minstCannotHaveTypeData
    validLet (MINST xs) CHAN       =  No minstCannotHaveTypeChan
    validLet (MINST xs) (PORT x)   =  No minstCannotHaveTypePort
    validLet (MINST xs) (MINST ys) =  No minstCannotHaveTypeMInst
    validLet (MINST xs) UNIT       =  No minstCannotHaveTypeUnit
    validLet (MINST xs) TYPE       =  No minstCannotHaveTypeType
    validLet (MINST xs) GATE         = No minstCannotHaveTypeGateLocal
    validLet (MINST xs) (GINST) = No minstCannotHaveTypeGInstLocal

    validLet UNIT (MODULE xs) = No unitCannotHaveTypeModule
    validLet UNIT DATA        = No unitCannotHaveTypeData
    validLet UNIT CHAN        = No unitCannotHaveTypeChan
    validLet UNIT (PORT x)    = No unitCannotHaveTypePort
    validLet UNIT (MINST xs)  = No unitCannotHaveTypeMInst
    validLet UNIT UNIT        = No unitCannotHaveTypeUnit
    validLet UNIT TYPE        = No unitCannotHaveTypeType
    validLet UNIT GATE         = No unitCannotHaveTypeGateLocal
    validLet UNIT (GINST) = No unitCannotHaveTypeGInstLocal

    validLet TYPE (MODULE xs) = No typeCannotHaveTypeModule
    validLet TYPE DATA        = No typeCannotHaveTypeData
    validLet TYPE CHAN        = No typeCannotHaveTypeChan
    validLet TYPE (PORT y)    = No typeCannotHaveTypePort
    validLet TYPE (MINST xs)  = No typeCannotHaveTypeMInst
    validLet TYPE UNIT        = No typeCannotHaveTypeUnit
    validLet TYPE TYPE        = No typeCannotHaveTypeType
    validLet TYPE GATE         = No typeCannotHaveTypeGateLocal
    validLet TYPE (GINST) = No typeCannotHaveTypeGInstLocal

    validLet GATE (MODULE xs)   = No gateCannotHaveTypeModuleLocal
    validLet GATE DATA          = No gateCannotHaveTypeDataLocal
    validLet GATE CHAN          = No gateCannotHaveTypeChanLocal
    validLet GATE (PORT y)      = No gateCannotHaveTypePortLocal
    validLet GATE (MINST xs)    = No gateCannotHaveTypeMInstLocal
    validLet GATE UNIT          = No gateCannotHaveTypeUnitLocal
    validLet GATE TYPE          = No gateCannotHaveTypeTypeLocal
    validLet GATE GATE          = No gateCannotHaveTypeGateLocal
    validLet GATE (GINST) = No gateCannotHaveTypeGInstLocal

    validLet (GINST) (MODULE xs)     = No ginstCannotHaveTypeModuleLocal
    validLet (GINST) DATA            = No ginstCannotHaveTypeDataLocal
    validLet (GINST) CHAN            = No ginstCannotHaveTypeChanLocal
    validLet (GINST) (PORT y)        = No ginstCannotHaveTypePortLocal
    validLet (GINST) (MINST xs)      = No ginstCannotHaveTypeMInstLocal
    validLet (GINST) UNIT            = No ginstCannotHaveTypeUnitLocal
    validLet (GINST) TYPE            = No ginstCannotHaveTypeTypeLocal
    validLet (GINST) GATE            = Yes IsLetGG
    validLet (GINST) GINST           = No ginstCannotHaveTypeGInstLocal

-- --------------------------------------------------------------------- [ EOF ]
