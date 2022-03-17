module Language.SystemVerilog.MetaTypes

import        Data.String

import public Toolkit.Data.DList.DeBruijn

%default total

public export
data Label : (s : String) -> Type where
  L : (s : String) -> Label s

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


-- ## DecEq

-- ### Uninabitents

Uninhabited (MODULE xs = DATA) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = CHAN) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = PORT p) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = MINST ys) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = UNIT) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = TYPE) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = GATE) where
  uninhabited Refl impossible

Uninhabited (MODULE xs = GINST) where
  uninhabited Refl impossible

Uninhabited (DATA = CHAN) where
  uninhabited Refl impossible

Uninhabited (DATA = PORT p) where
  uninhabited Refl impossible

Uninhabited (DATA = MINST ys) where
  uninhabited Refl impossible

Uninhabited (DATA = UNIT) where
  uninhabited Refl impossible

Uninhabited (DATA = TYPE) where
  uninhabited Refl impossible

Uninhabited (DATA = GATE) where
  uninhabited Refl impossible

Uninhabited (DATA = GINST) where
  uninhabited Refl impossible

Uninhabited (CHAN = PORT p) where
  uninhabited Refl impossible

Uninhabited (CHAN = MINST ys) where
  uninhabited Refl impossible

Uninhabited (CHAN = UNIT) where
  uninhabited Refl impossible

Uninhabited (CHAN = TYPE) where
  uninhabited Refl impossible

Uninhabited (CHAN = GATE) where
  uninhabited Refl impossible

Uninhabited (CHAN = GINST) where
  uninhabited Refl impossible

Uninhabited (PORT p = MINST ys) where
  uninhabited Refl impossible

Uninhabited (PORT p = UNIT) where
  uninhabited Refl impossible

Uninhabited (PORT p = TYPE) where
  uninhabited Refl impossible

Uninhabited (PORT p = GATE) where
  uninhabited Refl impossible

Uninhabited (PORT p = GINST) where
  uninhabited Refl impossible

Uninhabited (MINST xs = UNIT) where
  uninhabited Refl impossible

Uninhabited (MINST xs = TYPE) where
  uninhabited Refl impossible

Uninhabited (MINST xs = GATE) where
  uninhabited Refl impossible

Uninhabited (MINST xs = GINST) where
  uninhabited Refl impossible

Uninhabited (UNIT = TYPE) where
  uninhabited Refl impossible

Uninhabited (UNIT = GATE) where
  uninhabited Refl impossible

Uninhabited (UNIT = GINST) where
  uninhabited Refl impossible

Uninhabited (TYPE = GATE) where
  uninhabited Refl impossible

Uninhabited (TYPE = GINST) where
  uninhabited Refl impossible

Uninhabited (GATE = GINST) where
  uninhabited Refl impossible

-- ### Declaration

decEq : (x,y : Ty) -> Dec (x = y)

-- ### Definition

decEq (MODULE xs) y with (y)
  decEq (MODULE xs) y | (MODULE ys)
    = case decEq xs ys of
        Yes Refl => Yes Refl
        No contra => No (\Refl => contra Refl)

  decEq (MODULE xs) y | DATA
    = No absurd
  decEq (MODULE xs) y | CHAN
    = No absurd
  decEq (MODULE xs) y | (PORT x)
    = No absurd
  decEq (MODULE xs) y | (MINST ys)
    = No absurd
  decEq (MODULE xs) y | UNIT
    = No absurd
  decEq (MODULE xs) y | TYPE
    = No absurd
  decEq (MODULE xs) y | GATE
    = No absurd
  decEq (MODULE xs) y | GINST
    = No absurd

decEq DATA y with (y)
  decEq DATA y | (MODULE xs)
    = No (negEqSym absurd)
  decEq DATA y | DATA
    = Yes Refl
  decEq DATA y | CHAN
    = No absurd
  decEq DATA y | (PORT x)
    = No absurd
  decEq DATA y | (MINST xs)
    = No absurd
  decEq DATA y | UNIT
    = No absurd
  decEq DATA y | TYPE
    = No absurd
  decEq DATA y | GATE
    = No absurd
  decEq DATA y | GINST
    = No absurd

decEq CHAN y with (y)
  decEq CHAN y | (MODULE xs)
    = No (negEqSym absurd)
  decEq CHAN y | DATA
    = No (negEqSym absurd)
  decEq CHAN y | CHAN
    = Yes Refl
  decEq CHAN y | (PORT x)
    = No absurd
  decEq CHAN y | (MINST xs)
    = No absurd
  decEq CHAN y | UNIT
    = No absurd
  decEq CHAN y | TYPE
    = No absurd
  decEq CHAN y | GATE
    = No absurd
  decEq CHAN y | GINST
    = No absurd

decEq (PORT x) y with (y)
  decEq (PORT x) y | (MODULE xs)
    = No (negEqSym absurd)
  decEq (PORT x) y | DATA
    = No (negEqSym absurd)
  decEq (PORT x) y | CHAN
    = No (negEqSym absurd)

  decEq (PORT x) y | (PORT z)
    = case decEq x z of
        Yes Refl => Yes Refl
        No  contra => No (\Refl => contra Refl)

  decEq (PORT x) y | (MINST xs)
    = No absurd
  decEq (PORT x) y | UNIT
    = No absurd
  decEq (PORT x) y | TYPE
    = No absurd
  decEq (PORT x) y | GATE
    = No absurd
  decEq (PORT x) y | GINST
    = No absurd

decEq (MINST xs) y with (y)
  decEq (MINST xs) y | (MODULE ys)
     = No (negEqSym absurd)
  decEq (MINST xs) y | DATA
    = No (negEqSym absurd)
  decEq (MINST xs) y | CHAN
    = No (negEqSym absurd)
  decEq (MINST xs) y | (PORT x)
    = No (negEqSym absurd)

  decEq (MINST xs) y | (MINST ys)
    = case decEq xs ys of
        Yes Refl => Yes Refl
        No contra => No (\Refl => contra Refl)

  decEq (MINST xs) y | UNIT
    = No absurd
  decEq (MINST xs) y | TYPE
    = No absurd
  decEq (MINST xs) y | GATE
    = No absurd
  decEq (MINST xs) y | GINST
    = No absurd

decEq UNIT y with (y)
  decEq UNIT y | (MODULE xs)
    = No (negEqSym absurd)
  decEq UNIT y | DATA
    = No (negEqSym absurd)
  decEq UNIT y | CHAN
    = No (negEqSym absurd)
  decEq UNIT y | (PORT x)
    = No (negEqSym absurd)
  decEq UNIT y | (MINST xs)
    = No (negEqSym absurd)

  decEq UNIT y | UNIT = Yes Refl

  decEq UNIT y | TYPE
    = No absurd
  decEq UNIT y | GATE
    = No absurd
  decEq UNIT y | GINST
    = No absurd

decEq TYPE y with (y)
  decEq TYPE y | (MODULE xs)
    = No (negEqSym absurd)
  decEq TYPE y | DATA
    = No (negEqSym absurd)
  decEq TYPE y | CHAN
    = No (negEqSym absurd)
  decEq TYPE y | (PORT x)
    = No (negEqSym absurd)
  decEq TYPE y | (MINST xs)
    = No (negEqSym absurd)
  decEq TYPE y | UNIT
    = No (negEqSym absurd)

  decEq TYPE y | TYPE = Yes Refl

  decEq TYPE y | GATE
    = No absurd
  decEq TYPE y | GINST
    = No absurd

decEq GATE y with (y)
  decEq GATE y | (MODULE xs)
    = No (negEqSym absurd)
  decEq GATE y | DATA
    = No (negEqSym absurd)
  decEq GATE y | CHAN
    = No (negEqSym absurd)
  decEq GATE y | (PORT x)
    = No (negEqSym absurd)
  decEq GATE y | (MINST xs)
    = No (negEqSym absurd)
  decEq GATE y | UNIT
    = No (negEqSym absurd)
  decEq GATE y | TYPE
    = No (negEqSym absurd)
  decEq GATE y | GATE
    = Yes Refl
  decEq GATE y | GINST
    = No absurd

decEq GINST y with (y)
  decEq GINST y | (MODULE xs)
    = No (negEqSym absurd)
  decEq GINST y | DATA
    = No (negEqSym absurd)
  decEq GINST y | CHAN
    = No (negEqSym absurd)
  decEq GINST y | (PORT x)
    = No (negEqSym absurd)
  decEq GINST y | (MINST xs)
    = No (negEqSym absurd)
  decEq GINST y | UNIT
    = No (negEqSym absurd)
  decEq GINST y | TYPE
    = No (negEqSym absurd)
  decEq GINST y | GATE
    = No (negEqSym absurd)
  decEq GINST y | GINST
    = Yes Refl

export
DecEq Ty where
 decEq = MetaTypes.decEq


namespace Validity
{-
  namespace ModuleInstantiation
    public export
    data ValidInst : (xs : List String)
              -> (ys : List (Pair Necessity String))
                    -> Type
      where
        Empty : ValidInst Nil Nil

        Use : (prf  : x = y)
           -> (rest : ValidInst     xs          ys)
                   -> ValidInst (x::xs) ((n,y)::ys)

        SkipE : (rest : ValidInst Nil           ys)
                     -> ValidInst Nil ((OPT,y)::ys)

        Skip : (prf  : Not (x = y))
            -> (rest : ValidInst (x::xs)           ys)
                    -> ValidInst (x::xs) ((OPT,y)::ys)

    Uninhabited (ValidInst (x::xs) Nil) where
      uninhabited Empty impossible

    Uninhabited (ValidInst Nil ((REQ,n)::rest)) where
      uninhabited Empty impossible

    usedWrongLater : (ValidInst       xs               ys  -> Void)
                   -> ValidInst (x :: xs) ((nec, x) :: ys) -> Void

    usedWrongLater f (Use Refl rest) = f rest
    usedWrongLater f (Skip prf rest) = prf Refl

    skippedWrongLater : (ValidInst (x :: xs) ys -> Void)
                      -> (x = y -> Void)
                      -> ValidInst (x :: xs) ((OPT, y) :: ys)
                      -> Void

    skippedWrongLater f g (Use Refl rest) = g Refl
    skippedWrongLater f g (Skip prf rest) = f rest

    export
    validInst : (xs : List String)
             -> (ys : List (Pair Necessity String))
                   -> Dec (ValidInst xs ys)
    validInst [] []
      = Yes Empty
    validInst [] ((REQ, y) :: xs)
      = No absurd

    validInst [] ((OPT, y) :: xs) with (validInst Nil xs)
      validInst [] ((OPT, y) :: xs) | (Yes prf)
        = Yes (SkipE prf)

      validInst [] ((OPT, y) :: xs) | (No contra)
        = No (\(SkipE rest) => contra rest)

    validInst (x :: xs) []
      = No absurd

    validInst (x :: xs) ((nec, y) :: ys) with (decEq x y)
      validInst (x :: xs) ((nec, x) :: ys) | (Yes Refl) with (validInst xs ys)
        validInst (x :: xs) ((nec, x) :: ys) | (Yes Refl) | (Yes prf)
          = Yes (Use Refl prf)

        validInst (x :: xs) ((nec, x) :: ys) | (Yes Refl) | (No contra)
          = No (usedWrongLater contra)

      validInst (x :: xs) ((REQ, y) :: ys) | (No contra)
        = No (\(Use Refl prf) => contra Refl)

      validInst (x :: xs) ((OPT, y) :: ys) | (No contra) with (validInst (x::xs) ys)
        validInst (x :: xs) ((OPT, y) :: ys) | (No contra) | (Yes prf)
          = Yes (Skip contra prf)

        validInst (x :: xs) ((OPT, y) :: ys) | (No contra) | (No f)
          = No (skippedWrongLater f contra)

-}

  namespace Decl
    public export
    data ValidDecl : (expr : Ty) -> (type : Ty) -> Type where
       IsDeclM : ValidDecl (MODULE names) TYPE
       IsDeclD : ValidDecl DATA           TYPE

    Uninhabited (ValidDecl CHAN type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl (PORT s) type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl (MINST xs) type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl UNIT type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl TYPE type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl GATE type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl GINST type) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr (MODULE ys)) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr DATA) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr CHAN) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr (PORT s)) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr (MINST ys)) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr UNIT) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr GINST) where
      uninhabited IsDeclM impossible

    Uninhabited (ValidDecl expr GATE) where
      uninhabited IsDeclM impossible

    export
    validDecl : (expr,type : Ty)
                          -> Dec (ValidDecl expr type)
    validDecl (MODULE xs) type with (type)
      validDecl (MODULE xs) type | (MODULE ys)
        = No absurd
      validDecl (MODULE xs) type | DATA
        = No absurd
      validDecl (MODULE xs) type | CHAN
        = No absurd
      validDecl (MODULE xs) type | (PORT x)
        = No absurd
      validDecl (MODULE xs) type | (MINST ys)
        = No absurd
      validDecl (MODULE xs) type | UNIT
        = No absurd
      validDecl (MODULE xs) type | TYPE
        = Yes IsDeclM
      validDecl (MODULE xs) type | GATE
        = No absurd
      validDecl (MODULE xs) type | GINST
        = No absurd

    validDecl DATA type with (type)
      validDecl DATA type | (MODULE xs)
        = No absurd
      validDecl DATA type | DATA
        = No absurd
      validDecl DATA type | CHAN
        = No absurd
      validDecl DATA type | (PORT x)
        = No absurd
      validDecl DATA type | (MINST xs)
        = No absurd
      validDecl DATA type | UNIT
        = No absurd
      validDecl DATA type | TYPE
        = Yes IsDeclD
      validDecl DATA type | GATE
        = No absurd
      validDecl DATA type | GINST
        = No absurd

    validDecl CHAN _
      = No absurd
    validDecl (PORT x) _
      = No absurd
    validDecl (MINST xs) _
      = No absurd
    validDecl UNIT _
      = No absurd
    validDecl TYPE _
      = No absurd
    validDecl GATE _
      = No absurd
    validDecl GINST _
      = No absurd

  namespace LetBinding
    public export
    data ValidLet : (expr : Ty) -> (type : Ty) -> Type where
       IsLetMM : (prf :                 xs  =         ys)
                     -> ValidLet (MINST xs)   (MODULE ys)

       IsLetCD : ValidLet CHAN DATA

       IsLetGG : ValidLet GINST GATE

       IsLetDecl : ValidDecl expr ty
                -> ValidLet  expr ty

    Uninhabited (ValidLet expr CHAN) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet expr (PORT s)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible


    Uninhabited (ValidLet expr (MINST xs)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet expr UNIT) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet expr GINST) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet type type) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (MODULE xs) DATA) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (PORT xs) type) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (MINST xs) DATA) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet UNIT type) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet TYPE type) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet GATE type) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet GINST DATA) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet DATA (MODULE xs)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet GINST (MODULE xs)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet CHAN (MODULE xs)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (MODULE ys) (MODULE xs)) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet DATA GATE) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet CHAN GATE) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (MODULE xs) GATE) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    Uninhabited (ValidLet (MINST xs) GATE) where
      uninhabited (IsLetDecl IsDeclM) impossible
      uninhabited (IsLetDecl IsDeclD) impossible

    export
    validLet : (expr : Ty)
            -> (type : Ty)
            -> Dec (ValidLet expr type)
    validLet GATE _
      = No absurd

    validLet TYPE _
      = No absurd

    validLet (PORT s) _
      = No absurd

    validLet UNIT _
      = No absurd

    validLet (MODULE ys) (MODULE xs)
      = No absurd
    validLet DATA (MODULE xs)
      = No absurd
    validLet CHAN (MODULE xs)
      = No absurd

    validLet (MINST ys) (MODULE xs) with (decEq ys xs)
      validLet (MINST ys) (MODULE xs) | (Yes prf)
        = Yes (IsLetMM prf)
      validLet (MINST ys) (MODULE xs) | (No contra)
        = No (\(IsLetMM prf) => contra prf)

    validLet GINST (MODULE xs)
      = No absurd

    validLet (MODULE xs) DATA
      = No absurd

    validLet DATA DATA
      = No absurd

    validLet CHAN DATA = Yes IsLetCD

    validLet (MINST xs) DATA
      = No absurd

    validLet GINST DATA
      = No absurd

    validLet _ CHAN
      = No absurd

    validLet _ (PORT x)
      = No absurd

    validLet _ (MINST xs)
      = No absurd

    validLet _ UNIT
      = No absurd
    validLet expr TYPE with (validDecl expr TYPE)
      validLet expr TYPE | (Yes prf)
        = Yes (IsLetDecl prf)
      validLet expr TYPE | (No contra)
        = No (\(IsLetDecl prf) => contra prf)

    validLet (MODULE xs) GATE
      = No absurd

    validLet DATA GATE
      = No absurd

    validLet CHAN GATE
      = No absurd

    validLet (MINST xs) GATE
      = No absurd

    validLet UNIT GATE
      = No absurd

    validLet GINST GATE
      = Yes IsLetGG

    validLet _ GINST
      = No absurd

-- --------------------------------------------------------------------- [ EOF ]
