module LightClick.Terms


import Data.List.Quantifiers
import Data.Vect
import Data.Vect.Elem

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.Location

import Language.SystemVerilog.Gates

import LightClick.Types
import LightClick.Connection

import LightClick.Error

%default total

namespace Usage

  public export
  data Used = FREE | USED

  public export
  data Usage : MTy -> Type where
    TyData : Usage DATA
    TyConn : Usage CONN
    TyGate : Usage GATE

    TyPort : Used -> Usage (PORT label)
    TyModule : DVect String (Usage . PORT) (S n) names
             -> Usage (MODULE names)

  public export
  initModule : (names : Vect (S n) String) -> Usage (MODULE names)
  initModule (x :: [])
    = TyModule [TyPort FREE]

  initModule (x :: (y :: xs)) with (initModule (y::xs))
    initModule (x :: (y :: xs)) | (TyModule z) = TyModule (TyPort FREE :: z)


  namespace Whole
    namespace Free
      mutual
        public export
        data IsFree : (usage : Usage type) -> Type where
          D : IsFree TyData
          C : IsFree TyConn
          G : IsFree TyGate

          P : IsFree (TyPort FREE)
          M : FreePorts ps -> IsFree (TyModule ps)

        Uninhabited (IsFree (TyPort USED)) where
          uninhabited D impossible

        public export
        data FreePorts : (us : DVect String (Usage . PORT) n names) -> Type where
          EmptyIsFree : FreePorts Nil
          PortIsFree : {ps : DVect String (Usage . PORT) n names}
                   -> { p : Usage (PORT name)}
                   -> IsFree p
                   -> FreePorts ps
                   -> FreePorts (p::ps)

      mutual
        export
        isFree : (usage : Usage type)
                       -> Dec (IsFree usage)
        isFree TyData = Yes D
        isFree TyConn = Yes C
        isFree TyGate = Yes G
        isFree (TyPort FREE) = Yes P
        isFree (TyPort USED) = No absurd
        isFree (TyModule x) with (freePorts x)
          isFree (TyModule x) | (Yes prf) = Yes (M prf)
          isFree (TyModule x) | (No contra) = No (\(M prf) => contra prf)

        tailNotFree : (FreePorts rest -> Void) -> FreePorts (ex :: rest) -> Void
        tailNotFree f (PortIsFree x y) = f y

        headNotFree : {rest : DVect String (Usage . PORT) n names}
                   -> (IsFree ex -> Void) -> FreePorts (ex :: rest) -> Void
        headNotFree f (PortIsFree x y) = f x

        freePorts : (us : DVect String (Usage . PORT) n names)
                      -> Dec (FreePorts us)
        freePorts [] = Yes EmptyIsFree
        freePorts (ex :: rest) with (isFree ex)
          freePorts (ex :: rest) | (Yes prf) with (freePorts rest)
            freePorts (ex :: rest) | (Yes prf) | (Yes x)
              = Yes (PortIsFree prf x)
            freePorts (ex :: rest) | (Yes prf) | (No contra)
              = No (tailNotFree contra)
          freePorts (ex :: rest) | (No contra)
            = No (headNotFree contra)



    export
    use : (usage : Usage type)
       -> (prf   : IsFree usage)
                -> Usage type
    use TyData D = TyData
    use TyConn C = TyConn
    use TyGate G = TyGate
    use (TyPort FREE) P = TyPort USED
    use (TyModule ps) (M x) = TyModule (useM ps)
      where
        useM : (xs : DVect String (Usage . PORT) n names)
                  -> DVect String (Usage . PORT) n names
        useM [] = []
        useM ((TyPort y) :: rest) = TyPort USED :: useM rest

  namespace Used
    mutual
      public export
      data IsUsed : (usage : Usage type) -> Type where
        D : IsUsed TyData
        C : IsUsed TyConn
        G : IsUsed TyGate

        P : IsUsed (TyPort USED)
        M : UsedPorts ps -> IsUsed (TyModule ps)

      Uninhabited (IsUsed (TyPort FREE)) where
        uninhabited D impossible

      public export
      data UsedPorts : (us : DVect String (Usage . PORT) n names) -> Type where
        Nil : UsedPorts Nil
        (::) : {ps : DVect String (Usage . PORT) n names}
            -> { p : Usage (PORT name)}
            -> IsUsed p
            -> UsedPorts ps
            -> UsedPorts (p::ps)

    mutual

      moduleFree : (UsedPorts x -> Void) -> IsUsed (TyModule x) -> Void
      moduleFree f (M y) = f y

      export
      isUsed : (usage : Usage type) -> Dec (IsUsed usage)
      isUsed TyData = Yes D
      isUsed TyConn = Yes C
      isUsed TyGate = Yes G
      isUsed (TyPort FREE) = No absurd
      isUsed (TyPort USED) = Yes P
      isUsed (TyModule x) with (usedPorts x)
        isUsed (TyModule x) | (Yes prf) = Yes (M prf)
        isUsed (TyModule x) | (No contra) = No (moduleFree contra)


      tailIsFree : (UsedPorts rest -> Void) -> IsUsed ex -> UsedPorts (ex :: rest) -> Void
      tailIsFree f x (y :: z) = f z

      headIsFree : {rest : DVect String (Usage . PORT) n names}
                -> (IsUsed ex -> Void) -> UsedPorts (ex :: rest) -> Void
      headIsFree f (x :: y) = f x

      usedPorts : (us : DVect String (Usage . PORT) n names)
                     -> Dec (UsedPorts us)
      usedPorts []
        = Yes []
      usedPorts (ex :: rest) with (isUsed ex)
        usedPorts (ex :: rest) | (Yes prf) with (usedPorts rest)
          usedPorts (ex :: rest) | (Yes prf) | (Yes x)
            = Yes (prf :: x)

          usedPorts (ex :: rest) | (Yes prf) | (No contra)
            = No (tailIsFree contra prf)
        usedPorts (ex :: rest) | (No contra)
          = No (headIsFree contra)

  namespace AtIndex
    public export
    data FreeAt : (ports : DVect String (Ty    . PORT) n names)
               -> (usage : DVect String (Usage . PORT) n names)
               -> (prf   : Elem name names)
                        -> Type
      where
        Here : {ps  : DVect String (Ty    . PORT) n names}
            -> {us  : DVect String (Usage . PORT) n names}
            -> (prf : IsFree u)
                   -> FreeAt (p::ps) (u::us) Here

        There : (rest : FreeAt     ps      us         later)
                     -> FreeAt (p::ps) (u::us) (There later)



    notFreeHere : {ps  : DVect String (Ty    . PORT) n names}
               -> {us  : DVect String (Usage . PORT) n names}
               -> (IsFree u -> Void)
               -> (FreeAt (p :: ps) (u :: us) Here)
               -> Void

    notFreeHere f (Here prf) = f prf

    notFreeLater : {ps  : DVect String (Ty    . PORT) n names}
                -> {us  : DVect String (Usage . PORT) n names}
                -> ((FreeAt       ps        us         later)  -> Void)
                ->  (FreeAt (p :: ps) (u :: us) (There later)) -> Void
    notFreeLater f (There rest) = f rest

    export
    isFreeAt : (ports : DVect String (Ty    . PORT) n names)
            -> (usage : DVect String (Usage . PORT) n names)
            -> (prf   : Elem name names)
                     -> Dec (FreeAt ports usage prf)
    isFreeAt (p :: ps) (u::us) Here with (isFree u)
      isFreeAt (p :: ps) (u::us) Here | (Yes prf)
        = Yes (Here prf)

      isFreeAt (p :: ps) (u::us) Here | (No contra)
        = No (notFreeHere contra)

    isFreeAt (p::ps) (u::us) (There later) with (isFreeAt ps us later)
      isFreeAt (p::ps) (u::us) (There later) | (Yes prf)
        = Yes (There prf)

      isFreeAt (p::ps) (u::us) (There later) | (No contra)
        = No (notFreeLater contra)

    export
    useAt : (ports : DVect String (Usage . PORT) n names)
         -> (prf   : Elem name names)
                  -> DVect String (Usage . PORT) n names
    useAt ((TyPort x) :: rest) Here
      = TyPort USED :: rest
    useAt (ex :: rest) (There later) with (useAt rest later)
      useAt (ex :: rest) (There later) | used
        = ex :: used

namespace Context

  public export
  data Item : Type where
    I : {mtype : MTy} -> Ty mtype -> Usage mtype -> Item



  public export
  initItem : (type : Ty mtype) -> (prf : Bindable mtype)-> Usage mtype
  initItem type IsData
    = TyData

  initItem (TyModule x) IsModule
    = (initModule _)


  public export
  data Init : (type : Ty mtype) -> (prf : Bindable mtype) -> Usage mtype -> Type
    where
      II : {type  : Ty       m}
        -> {prf   : Bindable m}
        -> (usage : Usage    m)
                 -> Init type prf u

  public export
  init : (type : Ty mtype)
      -> (prf  : Bindable mtype)
              -> Init type prf (initItem type prf)
  init ty p
    = II (initItem ty p)

  public export
  data IsFree : (item : Item) -> Type where
    Free : IsFree u -> IsFree (I t u)

  export
  isFree : (item : Item) -> Dec (IsFree item)
  isFree (I x y) with (isFree y)
    isFree (I x y) | (Yes prf) = Yes (Free prf)
    isFree (I x y) | (No contra) = No (\(Free prf) => contra prf)

  public export
  data IsUsed : (item : Item) -> Type where
    Used : IsUsed u -> IsUsed (I t u)

  export
  isUsed : (item : Item) -> Dec (IsUsed item)
  isUsed (I x y) with (isUsed y)
    isUsed (I x y) | (Yes prf) = Yes (Used prf)
    isUsed (I x y) | (No contra) = No (\(Used prf) => contra prf)

  mutual
    public export
    data CanStop : (item : Item) -> Type where
      D : CanStop (I tyData TyData)
      C : CanStop (I TyConn TyConn)
      G : CanStop (I TyGate TyGate)

      PR : CanStop (I (TyPort k d s w Required type) (TyPort USED))
      PO : CanStop (I (TyPort k d s w Optional type) (TyPort u))

      M : CanStopPorts ports usages
       -> CanStop (I (TyModule ports) (TyModule usages))

    Uninhabited (CanStop (I (TyPort k d s w Required type) (TyPort FREE))) where
      uninhabited D impossible

    public export
    data CanStopPorts : (ports  : DVect String (Ty    . PORT) n names)
                     -> (usages : DVect String (Usage . PORT) n names)
                               -> Type
      where
       CSNil : CanStopPorts Nil Nil
       CSAdd : {ps : DVect String (Ty    . PORT) n names}
            -> {us : DVect String (Usage . PORT) n names}
            -> (x  : CanStop (I p u))
            -> (xs : CanStopPorts ps us)
                  -> CanStopPorts (p::ps) (u::us)
  mutual
    export
    canStop : (item : Item) -> Dec (CanStop item)
    canStop (I ty u) = canStop' ty u

    canStop' : (type  : Ty    m)
            -> (usage : Usage m)
                     -> Dec (CanStop (I type usage))

    canStop' x TyData
      = Yes D
    canStop' TyConn TyConn
      = Yes C
    canStop' TyGate TyGate
      = Yes G

    canStop' (TyPort label dir sense wty Required type) (TyPort FREE)
      = No absurd
    canStop' (TyPort label dir sense wty Required type) (TyPort USED)
      = Yes PR

    canStop' (TyPort label dir sense wty Optional type) (TyPort y)
      = Yes PO

    canStop' (TyModule x) (TyModule y) with (canStopPorts x y)
      canStop' (TyModule x) (TyModule y) | (Yes prf)
        = Yes (M prf)

      canStop' (TyModule x) (TyModule y) | (No contra)
        = No (\(M prf) => contra prf)

    canStopPorts : (ports  : DVect String (Ty    . PORT) n names)
                -> (usages : DVect String (Usage . PORT) n names)
                          -> Dec (CanStopPorts ports usages)
    canStopPorts [] []
      = Yes CSNil
    canStopPorts (p::ps) (u :: us) with (canStop' p u)
      canStopPorts (p::ps) (u :: us) | (Yes prf) with (canStopPorts ps us)
        canStopPorts (p::ps) (u :: us) | (Yes prf) | (Yes x)
          = Yes (CSAdd prf x)

        canStopPorts (p::ps) (u :: us) | (Yes prf) | (No contra)
          = No (\(CSAdd x xs) => contra xs)

      canStopPorts (p::ps) (u :: us) | (No contra)
        = No (\(CSAdd x xs) => contra x)

  public export
  Context : Type
  Context = List Item

  ||| Is the variable free?
  |||
  ||| We do not have a corresponding proof as we will derive it durning type-checking
  public export
  data FreeVar : Item -> Context -> Type where
    Here : (prf : IsFree i)
               -> FreeVar i (i::is)
    There : (rest : FreeVar i is)
                 -> FreeVar i (i'::is)

  ||| Update the context.
  |||
  ||| We do not use the corresponding proof as we will derive this predicate during type-checking
  public export
  data UseFreeVar : (old : Context)
                 -> (prf : FreeVar i old)
                 -> (new : Context)
                        -> Type
    where
      UH : (prfU : IsFree u)
               -> UseFreeVar (I type u            :: rest)
                             (Here (Free prfU))
                             (I type (use u prfU) :: rest)

      UT : UseFreeVar       old         later        new
        -> UseFreeVar (o :: old) (There later) (o :: new)

  ||| Update the context.
  export
  use : (old : Context)
     -> (prf : FreeVar i old)
            -> DPair Context (UseFreeVar old prf)
  use ((I t u) :: is) (Here (Free x))
    = MkDPair (I t (use u x) :: is) (UH x)

  use (i' :: is) (There rest) with (use is rest)
    use (i' :: is) (There rest) | (MkDPair fst snd)
      = MkDPair (i' :: fst) (UT snd)

  namespace FreePort

    public export
    data FreeElem : (label : String)
                 -> (ports : DVect String (Ty    . PORT) n names)
                 -> (usage : DVect String (Usage . PORT) n names)
                 -> Type
      where
        FE : {names : Vect n String}
          -> {ports : DVect String (Ty    . PORT) n names}
          -> {usage : DVect String (Usage . PORT) n names}
          -> (idx   : Elem label names)
          -> (prf   : FreeAt         ports usage idx)
                   -> FreeElem label ports usage

    Uninhabited (FreeElem label Nil Nil) where
      uninhabited (FE _ (Here prf)) impossible
      uninhabited (FE _ (There rest)) impossible

    notFreeHereThere : (FreeElem label ps us -> Void) -> (IsFree u -> Void) -> FreeElem label (TyPort label dir sense wty n type :: ps) (u :: us) -> Void
    notFreeHereThere f g (FE Here (Here prf)) = g prf
    notFreeHereThere f g (FE (There later) (There rest)) = f (FE later rest)

    notFreeLater : (FreeElem label ps us -> Void) -> (label = x -> Void) -> FreeElem label (TyPort x dir sense wty n type :: ps) (u :: us) -> Void
    notFreeLater f g (FE Here prf) = g Refl
    notFreeLater f g (FE (There later) (There rest)) = f (FE later rest)

    isFreeElem : {names : Vect n String}
              -> (label : String)
              -> (ports : DVect String (Ty    . PORT) n names)
              -> (usage : DVect String (Usage . PORT) n names)
                       -> Dec (FreeElem label ports usage)
    isFreeElem label Nil Nil
      = No absurd

    isFreeElem label ((TyPort x dir sense wty n type)::ps) (u::us) with (decEq label x)
      isFreeElem label ((TyPort label dir sense wty n type)::ps) (u::us) | (Yes Refl) with (isFree u)
        isFreeElem label ((TyPort label dir sense wty n type)::ps) ((TyPort FREE)::us) | (Yes Refl) | (Yes P)
          = Yes (FE Here (Here P))
        isFreeElem label ((TyPort label dir sense wty n type)::ps) (u::us) | (Yes Refl) | (No contra) with (isFreeElem label ps us)
          isFreeElem label ((TyPort label dir sense wty n type)::ps) (u::us) | (Yes Refl) | (No contra) | (Yes (FE idx prf))
            = Yes (FE (There idx) (There prf))
          isFreeElem label ((TyPort label dir sense wty n type)::ps) (u::us) | (Yes Refl) | (No contra) | (No f)
            = No (notFreeHereThere f contra)

      isFreeElem label ((TyPort x dir sense wty n type)::ps) (u::us) | (No contra) with (isFreeElem label ps us)
        isFreeElem label ((TyPort x dir sense wty n type)::ps) (u::us) | (No contra) | (Yes (FE idx prf))
          = Yes (FE (There idx) (There prf))
        isFreeElem label ((TyPort x dir sense wty n type)::ps) (u::us) | (No contra) | (No f)
          = No (notFreeLater f contra)


    public export
    data IsFreePort : (label : String)
                   -> (item  : Item)
                            -> Type
      where
        IFP : {ports : DVect String (Ty    . PORT) (S n) names}
           -> {usage : DVect String (Usage . PORT) (S n) names}
           -> (prf   : FreeElem label ports usage)
                    -> IsFreePort label (I (TyModule ports) (TyModule usage))

    Uninhabited (IsFreePort label (I TyLogic u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I (TyEnum as) u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I (TyArray ty l) u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I (TyStruct kvs) u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I (TyUnion kvs) u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I TyConn u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I TyUnit u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I TyGate u)) where
      uninhabited (IFP prf) impossible

    Uninhabited (IsFreePort label (I (TyPort x d s w n t) u)) where
      uninhabited (IFP prf) impossible

    export
    isFreePort : (label : String)
              -> (item  : Item)
                       -> Dec (IsFreePort label item)

    isFreePort label (I TyLogic u)
      = No absurd

    isFreePort label (I (TyEnum c) u)
      = No absurd

    isFreePort label (I (TyArray type l) u)
      = No absurd

    isFreePort label (I (TyStruct kvs) u)
      = No absurd

    isFreePort label (I (TyUnion kvs) u)
      = No absurd

    isFreePort label (I TyUnit u) = No absurd
    isFreePort label (I TyConn u) = No absurd
    isFreePort label (I TyGate u) = No absurd

    isFreePort label (I (TyPort x dir sense wty n type) u)
      = No absurd

    isFreePort label (I (TyModule ps) (TyModule us)) with (isFreeElem label ps us)
      isFreePort label (I (TyModule ps) (TyModule us)) | (Yes prf)
        = Yes (IFP prf)
      isFreePort label (I (TyModule ps) (TyModule us)) | (No contra)
        = No (\(IFP prf) => contra prf)




    ||| Is the variable free?
    |||
    ||| We do not have a corresponding proof as we will derive it turning type-checking
    public export
    data FreePort : (label : String)
                 -> (item  : Item)
                 -> (ctxt  : Context)
                          -> Type
      where
        Here : (prf   : IsFreePort label i)
                     -> FreePort   label i (i :: rest)

        There : (later : FreePort label item              rest )
                      -> FreePort label item (not_item :: rest)

    public export
    data UseFreePort : (old : Context)
                    -> (prf : FreePort label item old)
                    -> (new : Context)
                           -> Type
      where
        UH : {names : Vect (S n) String}
          -> {ports : DVect String (Ty    . PORT) (S n) names}
          -> {usage : DVect String (Usage . PORT) (S n) names}
          -> (idx   : Elem label names)
          -> (prfU  : FreeAt         ports usage idx)
                   -> UseFreePort (I (TyModule ports) (TyModule usage) :: rest)
                                  (Here (IFP (FE idx prfU)))
                                  (I (TyModule ports) (TyModule (useAt usage idx)) :: rest)

        UT : UseFreePort       old         later        new
          -> UseFreePort (o :: old) (There later) (o :: new)

    ||| Update the context.
    export
    use : (old : Context)
       -> (prf : FreePort l i old)
              -> DPair Context (UseFreePort old prf)
    use ((I (TyModule ports) (TyModule usage)) :: rest) (Here (IFP (FE idx prf)))
      = MkDPair (I (TyModule ports) (TyModule (useAt usage idx)) :: rest) (UH idx prf)

    use (not_item :: rest) (There later) with (use rest later)
      use (not_item :: rest) (There later) | (MkDPair fst snd)
        = MkDPair (not_item :: fst) (UT snd)



mutual
  namespace Fan
    public export
    data Fan : (old   : Context)
            -> (n     : Nat)
            -> {names : Vect n String}
            -> (ports : DVect String (Ty . PORT) n names)
            -> (new   : Context)
                     -> Type
      where
        Empty : Fan old Z Nil old

        Extend : {a,b,c : Context}
              -> {type  : Ty (PORT l)}
              -> {types : DVect String (Ty . PORT) n ls}
              -> (term  : Term a        type           b)
              -> (rest  : Fan  b n              types  c)
                       -> Fan  a (S n) (type :: types) c

  namespace Fields
    public export
    data Fields : (old  : List Item)
               -> (n    : Nat)
               -> (type : Vect n (Pair String (Ty DATA)))
               -> (new  : List Item)
                       -> Type
      where
        Empty : Fields ctxt Z Nil ctxt

        Extend : {a,b,c : Context}
              -> (s    : String)
              -> {type : Ty DATA}
              -> (tm   : Term   a           type          b)
              -> (rest : Fields b   n              types  c)
                      -> Fields a (S n) ((s,type)::types) c

  namespace Ports
    public export
    data Ports : (old   : List Item)
              -> (n     : Nat)
              -> {names : Vect n String}
              -> (types : DVect String (Ty . PORT) n names)
              -> (new   : List Item)
                       -> Type
      where
        Empty : Ports ctxt Z Nil ctxt
        Extend : {a,b,c : Context}
              -> {type  : Ty (PORT s)}
              -> {rest  : DVect String (Ty . PORT) n names}
              -> (port  : Term  a        type          b)
              -> (later : Ports b    n           rest  c)
                       -> Ports a (S n) (type :: rest) c

  public export
  data Term : (old  : Context)
           -> (item : Ty mtype)
           -> (new  : Context)
           -> Type
     where
       -- ## Core structures

       Ref : (fc  : FileContext)
          -> (l   : String)
          -> (prf : FreeVar (I type usage) old)
          -> (use : UseFreeVar old prf new)
                 -> Term old type new


       Let : {mtype  : MTy}
          -> {typeE  : Ty mtype}
          -> (fc     : FileContext)
          -> (label  : String)
          -> (this   : Term old typeE new)
          -> (prf    : Bindable mtype)
          -> {u      : Usage mtype}
          -> (newI   : Init typeE prf u)
          -> (inThis : Term (I typeE u :: old) TyUnit Nil)
                    -> Term old TyUnit Nil

       Seq : {type  : MTy}
          -> {typeA : Ty type}
          -> {a,b,c : Context}
          -> (this  : Term a typeA  b)
          -> (prf   : Seqable type)
          -> (that  : Term b TyUnit c)
                   -> Term a TyUnit c

       -- ## Data

       DataLogic : (fc : FileContext)
                      -> Term ctxt TyLogic ctxt

       DataEnum : {n : Nat}
               -> (fc : FileContext)
               -> (xs : Vect (S n) String)
                     -> Term ctxt (TyEnum xs) ctxt

       DataArray : (fc   : FileContext)
                -> (size : Nat)
                -> (type : Term a          dtype       b)
                        -> Term a (TyArray dtype size) b

       DataStruct : {n       : Nat}
                 -> {kvpairs : Vect (S n) (Pair String (Ty DATA))}
                 -> (fc      : FileContext)
                 -> (xs      : Fields a (S n)           kvpairs  b)
                            -> Term   a       (TyStruct kvpairs) b

       DataUnion : {n       : Nat}
                -> {kvpairs : Vect (S n) (Pair String (Ty DATA))}
                -> (fc      : FileContext)
                -> (xs      : Fields a (S n)          kvpairs  b)
                           -> Term   a       (TyUnion kvpairs) b

       -- ## Ports & Modules
       Port : (fc : FileContext)
           -> (l  : String)
           -> (d  : Direction)
           -> (s  : Sensitivity)
           -> (w  : Wire)
           -> (n  : Necessity)
           -> (i  : Term a                   dtype  b)
                 -> Term a (TyPort l d s w n dtype) b

       Module : {n     : Nat}
             -> {names : Vect (S n) String}
             -> {types : DVect String (Ty . PORT) (S n) names}

             -> (fc    : FileContext)
             -> (ports : Ports a (S n)           types  b)
                      -> Term  a       (TyModule types) b

       Index : {n : Nat}
            -> (fc   : FileContext)
            -> {names : Vect (S n) String}
            -> {typeM : Ty (MODULE names)}
            -> {usage : Usage (MODULE names)}
            -> (mref  : String)
            -> (label : String)
            -> (prf   : FreePort label (I typeM usage) a)
            -> (use   : UseFreePort a prf b)
            -> {port  : Ty (PORT label)}
            -> (getP  : HasPortNamed label typeM port)
                     -> Term a port b

       -- ## Connections

       NoOp : {a,b   : Context}
           -> {name  : String}
           -> (fc    : FileContext) -- derived from end of spec
           -> {type  : Ty (PORT name)}
           -> (term  : Term a type  b)
                    -> Term a TyConn b

       Connect : {a,b,c : Context}
              -> {pa,pb : String}
              -> {typeA : Ty (PORT pa)}
              -> {typeB : Ty (PORT pb)}
              -> (fc    : FileContext)
              -> (left  : Term a typeA b)
              -> (right : Term b typeB c)
              -> (prf   : Compatible typeA typeB)
                       -> Term a TyConn c


       FanOut : {a,b,c  : Context}
             -> {n      : Nat}
             -> {i      : String}
             -> {typeIn : Ty (PORT i)}
             -> {names  : Vect  (S (S n)) String}
             -> {ports  : DVect String (Ty . PORT) (S (S n)) names}
             -> (fc     : FileContext)
             -> (input  : Term a           typeIn b)
             -> (fan    : Fan  b (S (S n)) ports  c)
             -> (prf    : Fanout.Compatible typeIn ports)
                       -> Term a TyConn c

       Mux : {a,b,c,d : Context}
          -> {n      : Nat}
          -> {names  : Vect (S (S n)) String}
          -> {ports  : DVect String (Ty . PORT) (S (S n)) names}

          -> (fc     : FileContext)
          -> (fan    : Fan a (S (S n)) ports b)

          -> {ctrlNa : String}
          -> {typeC  : Ty (PORT ctrlNa)}
          -> (ctrl   : Term b typeC c)

          -> {outNa  : String}
          -> {typeO  : Ty (PORT outNa)}
          -> (output : Term c typeO d)

          -> (prf    : Compatible ports typeC typeO)

                    -> Term a TyConn d

       NOT : {a,b,c : Context}
          -> {an,bn : String}
          -> (fc    : FileContext)
          -> {typeA : Ty (PORT an)}
          -> {typeB : Ty (PORT bn)}

          -> (left  : Term a typeA b)
          -> (right : Term b typeB c)

          -> (prf   : Compatible typeA typeB)

                   -> Term a TyGate c


       GATE : {a,b,c : Context}
           -> {n : Nat}

           -> {names : Vect (S (S n)) String}
           -> {ports  : DVect String (Ty . PORT) (S (S n)) names}

           -> (fc    : FileContext)
           -> (ty    : TyGateComb)

           -> (fan    : Fan  a (S (S n)) ports b)

           -> {oname  : String}
           -> {typeO  : Ty (PORT oname)}
           -> (output : Term b typeO c)

           -> (prf    : Fanin.Compatible ports typeO)
                     -> Term a TyGate c

       End : (fc : FileContext) -> All IsUsed ctxt -> Term ctxt TyUnit Nil

export
getFC : Term old type new -> FileContext
getFC (Ref fc l prf use)                = fc
getFC (Let fc label this prf o inThis)  = fc
getFC (Seq this prf that)               = getFC this
getFC (DataLogic fc)                    = fc
getFC (DataEnum fc _)                   = fc
getFC (DataArray fc size x)             = fc
getFC (DataStruct fc xs)                = fc
getFC (DataUnion fc xs)                 = fc
getFC (Port fc l d s w n i)             = fc
getFC (Module fc ports)                 = fc
getFC (Index fc _ _ _ _ _)              = fc
getFC (Connect fc left right prf)       = fc
getFC (FanOut fc input fan prf)         = fc
getFC (Mux fc fan ctrl output prf)      = fc
getFC (NOT fc left right prf)           = fc
getFC (GATE fc ty fan output prf)       = fc
getFC (NoOp fc p)                       = fc
getFC (End fc x)                        = fc

-- [ EOF ]
