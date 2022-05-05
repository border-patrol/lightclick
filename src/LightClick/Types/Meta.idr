||| MetaTyping definitions.
|||
||| Module    : Meta.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.Types.Meta

import Data.Vect

import Toolkit.Data.Vect.Extra

%default total

public export
data MTy : Type where
  PORT : String -> MTy
  UNIT : MTy
  MODULE : {n : _} -> (Vect (S n) String) -> MTy
  CONN : MTy
  DATA : MTy
  GATE : MTy

-- [ Instances ]

export
Show MTy where
  show (PORT s)    = "(MTyPort " <+> s <+> ")"
  show UNIT        = "(MTyUnit)"
  show (MODULE ns) = "(MTyModule " <+> show ns <+> ")"
  show CONN        = "(MTyConnection)"
  show DATA        = "(MTyData)"
  show GATE        = "(MTyGate)"

export
show' : MTy -> String
show' (PORT s)    = "(MTyPort)"
show' UNIT        = "(MTyUnit)"
show' (MODULE ns) = "(MTyModule)"
show' CONN        = "(MTyConnection)"
show' DATA        = "(MTyData)"
show' GATE        = "(MTyGate)"

export
Eq MTy where
  (==) (PORT x)    (PORT y)    = x == y
  (==) UNIT        UNIT        = True
  (==) (MODULE xs) (MODULE ys) = vecEq xs ys
  (==) CONN        CONN        = True
  (==) DATA        DATA        = True
  (==) GATE        GATE        = True
  (==) _ _ = False


-- [ Uninhabitants ]

portLabelMismatch : (contra : (x = y) -> Void)
                 -> (PORT x = PORT y)
                 -> Void
portLabelMismatch contra Refl = contra Refl

vecsAreDiff : {xs : Vect (S n) String}
           -> {ys : Vect (S m) String}
           -> (contra : (xs = ys) -> Void)
           -> (MODULE xs = MODULE ys)
           -> Void
vecsAreDiff contra Refl = contra Refl


noPortUnit : (PORT s = UNIT) -> Void
noPortUnit Refl impossible

noPortModule : (PORT s = MODULE ns) -> Void
noPortModule Refl impossible

noPortConn : (PORT s = CONN) -> Void
noPortConn Refl impossible

noPortData : (PORT s = DATA) -> Void
noPortData Refl impossible

noPortGate : (PORT s = GATE) -> Void
noPortGate Refl impossible

noUnitConn : (UNIT = CONN) -> Void
noUnitConn Refl impossible

noUnitModule : (UNIT = MODULE xs) -> Void
noUnitModule Refl impossible

noUnitData : (UNIT = DATA) -> Void
noUnitData Refl impossible

noUnitGate : (UNIT = GATE) -> Void
noUnitGate Refl impossible

noModuleConn : (MODULE xs = CONN) -> Void
noModuleConn Refl impossible

noModuleData : (MODULE xs = DATA) -> Void
noModuleData Refl impossible

noModuleGate : (MODULE xs = GATE) -> Void
noModuleGate Refl impossible

noConnData : (CONN = DATA) -> Void
noConnData Refl impossible

noConnGate : (CONN = GATE) -> Void
noConnGate Refl impossible

noDataGate : (DATA = GATE) -> Void
noDataGate Refl impossible

-- [ Decision Procedure ]

export
DecEq MTy where
  decEq (PORT x) x2 with (x2)
    decEq (PORT x) x2 | (PORT y) with (decEq x y)
      decEq (PORT y) x2 | (PORT y) | (Yes Refl) = Yes Refl
      decEq (PORT x) x2 | (PORT y) | (No contra) = No (portLabelMismatch contra)
    decEq (PORT x) x2 | UNIT        = No (noPortUnit)
    decEq (PORT x) x2 | (MODULE xs) = No (noPortModule)
    decEq (PORT x) x2 | CONN        = No (noPortConn)
    decEq (PORT x) x2 | DATA        = No noPortData
    decEq (PORT x) x2 | GATE        = No noPortGate

  decEq UNIT x2 with (x2)
    decEq UNIT x2 | (PORT s)    = No (negEqSym noPortUnit)
    decEq UNIT x2 | UNIT        = Yes Refl
    decEq UNIT x2 | (MODULE xs) = No (noUnitModule)
    decEq UNIT x2 | CONN        = No (noUnitConn)
    decEq UNIT x2 | DATA        = No (noUnitData)
    decEq UNIT x2 | GATE        = No (noUnitGate)

  decEq (MODULE xs) x2 with (x2)
    decEq (MODULE xs) x2 | (PORT s)    = No (negEqSym noPortModule)
    decEq (MODULE xs) x2 | UNIT        = No (negEqSym noUnitModule)
    decEq (MODULE xs) x2 | (MODULE ys) with (decEq xs ys)
      decEq (MODULE ys) x2 | (MODULE ys) | (Yes Refl) = Yes Refl
      decEq (MODULE xs) x2 | (MODULE ys) | (No contra) = No (vecsAreDiff contra)

    decEq (MODULE xs) x2 | CONN        = No (noModuleConn)
    decEq (MODULE xs) x2 | DATA        = No (noModuleData)
    decEq (MODULE xs) x2 | GATE        = No (noModuleGate)

  decEq CONN x2 with (x2)
    decEq CONN x2 | (PORT s)    = No (negEqSym noPortConn)
    decEq CONN x2 | UNIT        = No (negEqSym noUnitConn)
    decEq CONN x2 | (MODULE ys) = No (negEqSym noModuleConn)
    decEq CONN x2 | CONN        = Yes Refl
    decEq CONN x2 | DATA        = No noConnData
    decEq CONN x2 | GATE        = No noConnGate

  decEq DATA x2 with (x2)
    decEq DATA x2 | (PORT s)    = No (negEqSym noPortData)
    decEq DATA x2 | UNIT        = No (negEqSym noUnitData)
    decEq DATA x2 | (MODULE ys) = No (negEqSym noModuleData)

    decEq DATA x2 | CONN        = No (negEqSym noConnData)
    decEq DATA x2 | DATA        = Yes Refl
    decEq DATA x2 | GATE        = No noDataGate

  decEq GATE x2 with (x2)
    decEq GATE x2 | (PORT s)    = No (negEqSym noPortGate)
    decEq GATE x2 | UNIT        = No (negEqSym noUnitGate)
    decEq GATE x2 | (MODULE ys) = No (negEqSym noModuleGate)

    decEq GATE x2 | CONN        = No (negEqSym noConnGate)
    decEq GATE x2 | DATA        = No (negEqSym noDataGate)
    decEq GATE x2 | GATE        = Yes Refl


-- [ EOF ]
