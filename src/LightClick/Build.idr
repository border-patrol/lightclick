module LightClick.Build

import Decidable.Equality

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect

import Toolkit.Decidable.Informative

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn
import Toolkit.Data.DVect

import Toolkit.DeBruijn.Context

import Toolkit.Data.Location

import Language.SystemVerilog.Gates
import Language.SystemVerilog.Utilities

import LightClick.Error
import LightClick.Core

import LightClick.Types
import LightClick.Types.Equality

import LightClick.Terms

import LightClick.Connection

import LightClick.DSL.AST

%default covering

Context : List Item -> Type
Context = Context Item


data Result : Context -> Type
  where
    R : {new    : Context}
     -> (mtype  : MTy)
     -> (type   : Ty mtype)
     -> (newEnv : Context new)
     -> (term   : Term old type new)
               -> Result old

data ResultFields : (ctxt : Context) -> Nat -> Type
  where
    RF : {n      : Nat}
      -> {new    : Context}
      -> (types  : Vect n (Pair String (Ty DATA)))
      -> (newEnv : Context new)
      -> (term   : Fields old n types new)
                -> ResultFields old n

data ResultData : (ctxt : Context) -> Type
  where
    RD : {new    : Context}
      -> (type   : Ty DATA)
      -> (newEnv : Context new)
      -> (term   : Term old type new)
                -> ResultData old

data ResultMRef : (ctxt : Context) -> Type
  where
    RM : {new    : Context}
      -> (mref   : String)
      -> (names  : Vect (S n) String)
      -> (type   : (Ty (MODULE names)))
      -> (newEnv : Context new)
      -> (term   : Term old type new)
                -> ResultMRef old

data ResultPort : (ctxt : Context) -> Type
  where
    Rp : {new    : Context}
      -> (l      : String)
      -> (type   : (Ty (PORT l)))
      -> (newEnv : Context new)
      -> (term   : Term old type new)
                -> ResultPort old

data ResultPorts : (ctxt : Context) -> Nat -> Type
  where
    RP : {n      : Nat}
      -> {new    : Context}
      -> {names  : Vect n String}
      -> (types  : DVect String (Ty . PORT) n names)
      -> (newEnv : Context new)
      -> (term   : Ports old n types new)
                -> ResultPorts old n

data ResultFans : (ctxt : Context) -> Nat -> Type
  where
    RFS : {n      : Nat}
       -> {new    : Context}
       -> {names  : Vect n String}
       -> (types  : DVect String (Ty . PORT) n names)
       -> (newEnv : Context new)
       -> (term   : Fan old n types new)
                 -> ResultFans old n

data ResultLeftSEQ : (ctxt : Context) -> Type
  where
    RLS : {new    : Context}
       -> {m      : MTy}
       -> (type   : Ty m)
       -> (newEnv : Context new)
       -> (term   : Term old type new)
       -> (prf    : Seqable m)
                 -> ResultLeftSEQ old

data ResultBind : (ctxt : Context) -> Type
  where
    RB : {new    : Context}
      -> {m      : MTy}
      -> (type   : Ty m)
      -> (newEnv : Context new)
      -> (term   : Term old type new)
      -> (prf    : Bindable m)
                -> ResultBind old

namespace GetModule

  data LookupFail = NotFound | NotAModule

  data IsModule : (str  : String)
               -> (item : Item Item i)
                       -> Type
    where
      IM : (prf   : x = y)
        -> {names : Vect (S n) String}
        -> {type  : Ty (MODULE names)}
        -> {u     : Usage (MODULE names)}
                -> IsModule x (I y (I type u))

  Uninhabited (IsModule str (I x (I TyLogic u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I TyUnit u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I TyConn u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I TyGate u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I (TyEnum xs) u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I (TyArray ty l) u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I (TyStruct kvs) u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I (TyUnion kvs) u))) where
    uninhabited (IM prf) impossible

  Uninhabited (IsModule str (I x (I (TyPort label dir sense wty n type) u))) where
    uninhabited (IM prf) impossible

  isModule : (str  : String)
          -> (item : Item Item i)
                  -> DecInfo LookupFail (IsModule str item)

  isModule str (I name i) with (decEq str name)
    isModule str (I str i) | (Yes Refl) with (i)
      isModule str (I str i) | (Yes Refl) | (I TyLogic y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyEnum kvs) y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyArray type length) y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyStruct kvs) y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyUnion kvs) y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I TyUnit y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I TyConn y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I TyGate y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyPort label dir sense wty n type) y)
        = No NotAModule absurd
      isModule str (I str i) | (Yes Refl) | (I (TyModule x) y)
        = Yes (IM Refl)

    isModule str (I name i) | (No contra)
      = No NotFound (\(IM Refl) => contra Refl)

  ModuleRef : {curr : Context}
           -> (name : String)
           -> (ctxt : Context curr)
                   -> Type
  ModuleRef str ctxt
    = Exists (IsModule str) ctxt

  lookup : (fc    : FileContext)
        -> (s     : String)
        -> {types : List Item}
        -> (ctxt  : Context types)
                 -> DecInfo (LightClick.Error)
                            (ModuleRef s ctxt)

  lookup fc s ctxt with (exists (isModule s) ctxt)
    lookup fc s ctxt | (Yes (B item prfP prfE))
      = Yes (B item prfP prfE)

    lookup fc s ctxt | (No msg contra)
        = No (newMsg msg) contra

      where
        newMsg : Error LookupFail -> LightClick.Error
        newMsg (NotSatisfied NotFound)
          = (IdentifierNotFound fc s)

        newMsg (NotSatisfied NotAModule)
          = (IdentifierNotFound fc s)

        newMsg NotFound
          = (IdentifierNotFound fc s)


  export
  moduleRef : {old : Context}
           -> (curr : Context old)
           -> (ast  : AST)
                   -> LightClick String
  moduleRef ctxt (Ref fc name)
    = do prf <- embed id (lookup fc name ctxt)
         pure name

  moduleRef ctxt _ = throw (NotSupposedToHappen (Just "Modules cannot be inlined."))


namespace FreeVar

  data LookupFail = NotFound String | IsUsed String

  data IsFree : String -> Item Item i -> Type where
    IF : (prf : x = y)
      -> (prfU : IsFree i)
              -> IsFree x (I y i)

  isFree : (str  : String)
        -> (item : Item Item i)
                -> DecInfo LookupFail
                           (IsFree str item)
  isFree str (I name i) with (decEq str name)
    isFree str (I str  i) | (Yes Refl) with (isFree i)
      isFree str (I str  i) | (Yes Refl) | (Yes prf)
        = Yes (IF Refl prf)
      isFree str (I str  i) | (Yes Refl) | (No contra)
        = No (IsUsed str)
             (\(IF Refl prf) => contra prf)

    isFree str (I name i) | (No contra)
      = No (NotFound name)
           (\(IF Refl pU) => contra Refl)

  FreeVar : {types : List Item} -> String -> Context types -> Type
  FreeVar str ctxt
    = Exists (IsFree str) ctxt


  lookup : (fc    : FileContext)
        -> (s     : String)
        -> {types : List Item}
        -> (ctxt  : Context types)
                 -> DecInfo (LightClick.Error)
                            (FreeVar s ctxt)

  lookup fc s ctxt with (exists (isFree s) ctxt)
    lookup fc s ctxt | (Yes (B item prfP prfE))
      = Yes (B item prfP prfE)

    lookup fc s ctxt | (No msg contra)
        = No (newMsg msg) (contra)
      where
        newMsg : (Error LookupFail) -> LightClick.Error
        newMsg (NotSatisfied (NotFound x))
          = IdentifierNotFound fc s
        newMsg (NotSatisfied (IsUsed x))
          = PortInUse fc s
        newMsg NotFound
          = IdentifierNotFound fc s

  transform : {s    : String}
           -> {curr : List Item}
           -> {ctxt : Context curr}
           -> (idx  : Any Item (Item Item) (Holds Item (IsFree s)) ctxt)
                   -> DPair Item (\i => FreeVar i curr)
  transform (H (H (IF prf prfU)))
    = MkDPair _ (Here prfU)
  transform (T contra later) with (transform later)
    transform (T contra later) | (MkDPair fst snd)
      = MkDPair fst (There snd)

  public export
  data UsedVar : (old : Context)
                     -> Type
    where
      UV : (m    : MTy)
        -> (ty   : Ty m)
        -> {new  : Context}
        -> (ctxt : Context new)
        -> {u    : Usage m}
        -> (idx  : FreeVar (I ty u) old)
        -> (prf  : UseFreeVar old idx new)
                -> UsedVar old

  useVar : {new : Context}
        -> (ctxt : Context old)
        -> {idx  : FreeVar i old}
        -> (prf  : UseFreeVar old idx new)
                -> Context new
  useVar (I n (I ty u) :: rest) (UH prfU)
    = I n (I ty (use u prfU)) :: rest

  useVar (elem :: rest) (UT x)
    = elem :: useVar rest x


  export
  freeVar : (fc   : FileContext)
         -> (s    : String)
         -> {curr : Context}
         -> (ctxt : Context curr)
                 -> LightClick (UsedVar curr)
  freeVar {curr} fc s ctxt
    = do (B _ _ idx') <- embed id (lookup fc s ctxt)
         let ((I ty u) ** idx) = transform idx'
         let (new ** prf) = use curr idx
         let newE = useVar ctxt prf
         pure (UV _ _ newE idx prf)

namespace FreePort
  data LookupFail = NotFound | IsUsed String

  isFreePort : (str : String)
            -> (i   : Item)
                   -> DecInfo LookupFail
                              (IsFreePort str i)
  isFreePort str i with (Context.FreePort.isFreePort str i)
    isFreePort str i | (Yes prf)
      = Yes prf

    isFreePort str i | (No contra)
      = No (IsUsed str) contra

  FreePort : {types : List Item} -> String -> String -> Context types -> Type
  FreePort mref label ctxt
    = ExistsFor (IsFreePort label) mref ctxt

  lookup : (fc         : FileContext)
        -> (mref,label : String)
        -> {types      : List Item}
        -> (ctxt       : Context types)
                      -> DecInfo (LightClick.Error)
                                 (FreePort mref label ctxt)
  lookup fc mref label ctxt with (existsFor (isFreePort label) mref ctxt)
    lookup fc mref label ctxt | (Yes prfWhy)
      = Yes prfWhy
    lookup fc mref label ctxt | (No msg contra)
        = No (newErr msg) contra
      where
        newErr : Error LookupFail -> LightClick.Error
        newErr (NotSatisfied NotFound)
          = IdentifierNotFound fc mref

        newErr (NotSatisfied (IsUsed x))
          = PortInUse fc x

        newErr NotFound
          = IdentifierNotFound fc mref

  transform : {m,l  : String}
           -> {curr : Context}
           -> {ctxt : Context curr}
           -> (idx  : Any Item (Item Item) (HoldsFor Item (IsFreePort l) m) ctxt)
                   -> DPair Item (\i => FreePort l i curr)
  transform (H (H4 prfK prf))
    = MkDPair _ (Here prf)

  transform (T contra later) with (transform later)
    transform (T contra later) | (MkDPair fst snd)
      = MkDPair fst (There snd)

  usePort : {old  : Context}
         -> (ctxt : Context old)
         -> {idx  : FreePort label i old}
         -> (prf  : UseFreePort old idx new)
                 -> Context new
  usePort ((I n (I (TyModule ports) (TyModule usage))) :: rest) (UH idx prf)
    = (I n (I (TyModule ports) (TyModule (useAt usage idx))) :: rest)

  usePort (elem :: rest) (UT x)
    = elem :: usePort rest x


  public export
  data UsedPort : String -> Context -> Type where
    UP : {n      : Nat}
      -> {new    : Context}
      -> {names  : Vect (S n) String}
      -> (typeM  : Ty (MODULE names))
      -> {u      : Usage (MODULE names)}
      -> (idx    : FreePort label (I typeM u) old)
      -> (prf    : UseFreePort old idx new)
      -> (ctxt   : Context new)
                -> UsedPort label old

  export
  usedPort : (fc         : FileContext)
          -> (mref,label : String)
          -> {old        : Context}
          -> (curr       : Context old)
                        -> LightClick (UsedPort label old)
  usedPort fc mref label curr {old}
    = do B4 _ _ idx' <- embed id (lookup fc mref label curr)

         let (I tyM um ** idx) = transform idx'
         case tyM of
           (TyModule ns)
             => do let (new ** prf) = use old idx
                   let newE = usePort curr prf

                   pure (UP (TyModule ns) idx prf newE)
           _ => throw (Err fc "Should not happen.")



isUsed : (ctxt : Context curr)
              -> Dec (All IsUsed curr)
isUsed []
  = Yes []

isUsed ((I name item) :: rest) with (isUsed item)
  isUsed ((I name item) :: rest) | (Yes prf) with (isUsed rest)
    isUsed ((I name item) :: rest) | (Yes prf) | (Yes x)
      = Yes (prf :: x)

    isUsed ((I name item) :: rest) | (Yes prf) | (No contra)
      = No (\(x::xs) => contra xs)
  isUsed ((I name item) :: rest) | (No contra)
    = No (\(x::xs) => contra x)

canStop : (ctxt : Context curr)
               -> Dec (All CanStop curr)
canStop []
  = Yes []

canStop ((I name item) :: rest) with (canStop item)
  canStop ((I name item) :: rest) | (Yes prf) with (canStop rest)
    canStop ((I name item) :: rest) | (Yes prf) | (Yes x)
      = Yes (prf :: x)

    canStop ((I name item) :: rest) | (Yes prf) | (No contra)
      = No (\(x::xs) => contra xs)
  canStop ((I name item) :: rest) | (No contra)
    = No (\(x::xs) => contra x)


namespace FindFree

  freeModulePorts : (p : DVect String (Ty    . PORT) n names)
                 -> (u : DVect String (Usage . PORT) n names)
                      -> List String
  freeModulePorts [] [] = []

  freeModulePorts ((TyPort x dir sense wty Required type) :: y) ((TyPort FREE) :: rest)
    = x :: freeModulePorts y rest

  freeModulePorts ((TyPort x dir sense wty n type) :: y) ((TyPort _) :: rest)
    = freeModulePorts y rest

  %inline
  getFree : Item
         -> List String


  getFree (I (TyPort label dir sense wty Required type) (TyPort FREE))
    = [label]

  getFree (I x (TyPort _))
    = Nil

  getFree (I (TyModule x) (TyModule y))
    = freeModulePorts x y

  getFree (I x _) = Nil

  export
  findFree : (ctxt : Context curr)
                  -> List ((String, List String))
  findFree [] = []
  findFree ((I name x) :: rest) with (getFree x)
    findFree ((I name x) :: rest) | [] = findFree rest
    findFree ((I name x) :: rest) | (y :: xs)
      = (name,(y::xs)) :: findFree rest

namespace FindNoOp

  freeModulePorts : (p : DVect String (Ty    . PORT) n names)
                 -> (u : DVect String (Usage . PORT) n names)
                      -> List String
  freeModulePorts [] [] = []
  freeModulePorts ((TyPort x dir sense wty Optional type) :: y) ((TyPort FREE) :: rest)
    = x :: freeModulePorts y rest

  freeModulePorts ((TyPort x dir sense wty n type) :: y) ((TyPort u) :: rest)
    = freeModulePorts y rest

  %inline
  getFree : Item
         -> List String


  getFree (I (TyPort label dir sense wty Optional type) (TyPort FREE))
    = [label]

  getFree (I x (TyPort _))
    = Nil

  getFree (I (TyModule x) (TyModule y))
    = freeModulePorts x y

  getFree (I x _) = Nil

  export
  findNoOps : (ctxt : Context curr)
                  -> List ((String, List String))
  findNoOps [] = []
  findNoOps ((I name x) :: rest) with (getFree x)
    findNoOps ((I name x) :: rest) | [] = findNoOps rest
    findNoOps ((I name x) :: rest) | (y :: xs)
      = (name,(y::xs)) :: findNoOps rest

noops : (fc   : FileContext)
     -> (ps   : List (String, List String))
             -> AST
noops fc ps
    = foldr Seq (End' fc) noops'
  where
    noop : (String, List String) -> List AST
    noop (mref, labels)
      = foldr (\label, acc => NoOp fc (Index fc (Ref fc mref) label) :: acc)
              Nil
              labels

    noops' : List AST
    noops' = foldr (\p, acc => noop p ++ acc) Nil ps

mutual

  datatype : {old   : Context}
          -> (ctxt  : Context old)
          -> (dtype : AST)
                   -> LightClick (ResultData old)
  datatype ctxt dtype
    = do R DATA type new dtype <- build ctxt dtype
           | R m _ _ tm => throw (MetaTypeConstructionError (Terms.getFC tm) DATA m)
         pure (RD type new dtype)

  portRef : {old  : Context}
         -> (ctxt : Context old)
         -> (port : AST)
                 -> LightClick (ResultPort old)
  portRef ctxt (Index fc y z)
    = do R (PORT l) type new p <- build ctxt (Index fc y z)
           | R m _ _ tm => throw (MetaTypeConstructionError (Terms.getFC tm) (PORT "") m)

         pure (Rp l type new p)

  portRef ctxt _ = throw (NotSupposedToHappen (Just "Ports are only accessible by projection"))

  portVal : {old  : Context}
         -> (ctxt : Context old)
         -> (port : AST)
                 -> LightClick (ResultPort old)
  portVal ctxt (Port fc l d s w n t)
    = do R (PORT l) type new p <- build ctxt (Port fc l d s w n t)
           | R m _ _ tm => throw (MetaTypeConstructionError (Terms.getFC tm) (PORT "") m)
         pure (Rp l type new p)

  portVal ctxt _ = throw (NotSupposedToHappen (Just "Module defs must contain raw ports."))

  ports : {old   : Context}
       -> (ctxt  : Context old)
       -> (seen  : List String)
       -> (ports : Vect (S n) AST)
                -> LightClick (ResultPorts old (S n))

  ports ctxt st (x :: [])
    = do Rp l type new p <- portVal ctxt x
         when (isElem l st) $ do
           throw (IdentifierAlreadyExists (getFC p) l)

         pure (RP [type] new (Extend p Empty))

  ports ctxt st (x :: (y :: xs))
    = do Rp l type newA p <- portVal ctxt x

         when (isElem l st) $ do
           throw (IdentifierAlreadyExists (getFC p) l)


         RP types newB ps <- ports newA (l::st) (y::xs)

         pure (RP (type::types)
                  newB
                  (Extend p ps))


  fans : {n      : Nat}
      -> {old    : Context}
      -> (env    : Context old)
      -> (fields : Vect (S (S n)) AST)
                -> LightClick (ResultFans old (S (S n)))
  fans env (a :: (b :: []))

    = do Rp aname tyA newE  a <- portRef env a

         Rp bname tyB newEE b <- portRef newE b

         pure (RFS [tyA, tyB]
                   newEE
                   (Extend a
                   (Extend b
                   (Empty))))


  fans env (a :: (b :: (c :: xs)))
    = do Rp aname tyA newE a <- portRef env a

         RFS types newEE rest <- fans newE (b :: c :: xs)

         pure (RFS (tyA::types)
                   newEE
                   (Extend a rest))


  fields : {n      : Nat}
        -> {old    : Context}
        -> (env    : Context old)
        -> (seen   : List String)
        -> (fields : Vect (S n) (String, AST))
                  -> LightClick (ResultFields old (S n))

  fields env st ((s, f) :: [])
    = do RD type newE tm <- datatype env f
         when (isElem s st) $ do
           throw (IdentifierAlreadyExists (getFC tm) s)

         pure (RF [(s,type)] newE (Extend s tm Empty))

  fields env st ((s, f) :: (x :: xs))
    = do RD ty newE tm <- datatype env f

         when (isElem s st) $ do
           throw (IdentifierAlreadyExists (getFC tm) s)

         RF tys newEE rest <- fields newE (s::st) (x::xs)

         pure (RF ((s,ty)::tys) newEE (Extend s tm rest))


  leftSEQ : {old  : Context}
         -> (curr : Context old)
         -> (ast  : AST)
                 -> LightClick (ResultLeftSEQ old)
  leftSEQ curr ast
    = do R m type new term <- build curr ast
         case m of
           GATE => pure (RLS type new term IsGate)
           CONN => pure (RLS type new term IsConn)
           _    => throw (Nest (Err (getFC term) "") (SeqError))


  bind : {old  : Context}
      -> (curr : Context old)
      -> (ast  : AST)
              -> LightClick (ResultBind old)
  bind curr tm
    = do R m type new term <- build curr tm
         case m of
           DATA      => pure (RB type new term IsData)
           MODULE ns => pure (RB type new term IsModule)
           _ => throw (Nest (Err (getFC term) "") (BindError))

  build : {ctxt : Context}
       -> (curr : Context ctxt)
       -> (ast  : AST)
               -> LightClick (Result ctxt)

  build curr (Ref fc name)
    = do UV m ty new idx prf <- freeVar fc name curr

         pure (R _ _ new (Ref fc name idx prf))

  build curr (Bind fc name tm scope)
    = do RB type new tm prf <- bind curr tm

         let II u = init type prf
         let newExt = extend new name (I type u)

         R UNIT TyUnit Nil scope <- build newExt scope
           | R _ _ (x::xs) tm
             => throw (NotSupposedToHappen Nothing)
           | R m _ _ tm
             => throw (MetaTypeConstructionError (Terms.getFC tm) UNIT m)

         pure (R UNIT TyUnit Nil (Let fc name tm prf (II u) scope))

  build curr (Seq x y)
    = do RLS type newA x prfLS <- leftSEQ curr x

         R UNIT TyUnit newB tY <- build newA y
           | R m _ _ tm => throw (MetaTypeConstructionError (Terms.getFC tm) UNIT m)

         pure (R _ _ newB (Seq x prfLS tY))


  -- [ DATATYPES ]
  build curr (DataLogic fc)
    = pure (R _ _ curr (DataLogic fc))

  build curr (DataEnum fc xs)
      = do xs' <- checkUnique Nil xs
           pure (R _ _ curr (DataEnum fc xs'))
    where
      checkUnique : List String
                 -> Vect m String
                 -> LightClick (Vect m String)
      checkUnique _ Nil
        = pure Nil
      checkUnique st (y::ys)
        = do when (isElem y st) $ do
               throw (IdentifierAlreadyExists fc y)
             ys <- checkUnique (y::st) ys
             pure (y::ys)

  build curr (DataArray fc type s)
    = do RD t outE type' <- datatype curr type
         pure (R _ _ outE (DataArray fc s type'))

  build curr (DataStruct fc kvs)
    = do RF tys end kvs' <- fields curr Nil kvs
         pure (R _ _ end (DataStruct fc kvs'))

  build curr (DataUnion fc kvs)
    = do RF tys end kvs' <- fields curr Nil kvs
         pure (R _ _ end (DataUnion fc kvs'))

  -- [ Ports & Modules ]

  build curr (Port fc label dir sense wty n type)
    = do RD t outE type' <- datatype curr type

         pure (R _ _ outE (Port fc label dir sense wty n type'))

  build curr (ModuleDef fc kvs)
    = do RP types newA ports <- ports curr Nil kvs
         pure (R _ _ newA (Module fc ports))

  build curr (Index fc mref label)
    = do name <- moduleRef curr mref

         UP tyM idx prf newE <- usedPort fc name label curr

         (p ** getP) <- embed (IdentifierNotFound fc label)
                              (hasPortNamed label tyM)

         pure (R _ p newE (Index fc name label idx prf getP))


  -- [ Connections ]
  build curr (Connect fc o i)
    = do Rp oname ot curr'  o <- portRef curr  o

         Rp iname it curr'' i <- portRef curr' i

         let err = (\msg => Nest (Mismatch fc ot it)
                                 (UnSafeDirectConnection fc msg))

         prf <- embed err (compatible ot it)

         pure (R _ _ curr'' (Connect fc o i prf))

  build curr (FanOut fc i fan)
    = do Rp iname typeI newA i <- portRef curr i

         RFS types newB fan <- fans newA fan

         let errFunc : PortList.Error -> LightClick.Error
             errFunc (PListError pos ty reason)
               = Nest (Mismatch  fc typeI ty)
                      (UnSafeFan fc FANOUT pos reason)

         prf <- embed errFunc
                      (Fanout.compatible typeI types)

         pure (R _ _ newB (FanOut fc i fan prf))

  build curr (Mux fc fan ctrl o)
    = do RFS types newE fan <- fans curr fan

         Rp cname typeC newEE  ctrl <- portRef newE  ctrl
         Rp oname typeO newEEE o    <- portRef newEE o

         let errFunc : Mux.Error -> LightClick.Error
             errFunc (CtrlNotSafe c x)
               = Nest (Mismatch fc c typeC)
                      (UnSafeMuxCtrl (getFC ctrl) x)

             errFunc (MuxNotSafe (PListError pos ty reason))
               = Nest (Mismatch fc ty typeO)
                      (UnSafeFan fc FANIN pos reason)


         prf <- embed errFunc
                      (Mux.compatible types typeC typeO)

         pure (R _ _ newEEE (Mux fc fan ctrl o prf))

  -- [ GATEs ]

  build curr (NOT fc i o)
    = do Rp iname it curr'  i' <- portRef curr  i

         Rp oname ot curr'' o' <- portRef curr' o

         let err = (\msg => Nest (Mismatch fc it ot)
                                 (UnSafeDirectConnection fc msg))

         prf <- embed err (compatible it ot)

         pure (R _ _ curr'' (NOT fc i' o' prf))


  build curr (GATE fc kind is o)
    = do RFS types newE is <- fans curr is
         Rp oname type newEE o <- portRef newE o

         let errFunc : PortList.Error -> LightClick.Error
             errFunc (PListError pos ty reason)
               = Nest (Mismatch fc ty type)
                      (UnSafeFan fc FANIN pos reason)

         prf <- embed errFunc
                      (Fanin.compatible types type)

         pure (R _ _ newEE (GATE fc kind is o prf))

  build curr (NoOp fc p)
    = do (Rp l type new p) <- portRef curr p
         pure (R _ _ new (NoOp fc (fromType type) p))
  -- [ The End ]

  build curr (End fc) with (canStop curr)
    build curr (End fc) | (Yes prfStop)
      = do let nps = noops fc (findNoOps curr)
           build curr nps


    build curr (End fc) | (No contra)
      = throw (UnusedPorts (findFree curr))

  build curr (End' fc) with (isUsed curr)
    build curr (End' fc) | (Yes prfStop)
      = pure (R _ _ Nil (End fc prfStop))

    build curr (End' fc) | (No contra)
      = throw (UnusedPorts (findFree curr))

export
termBuilder : (ast : AST)
                  -> LightClick (Term Nil TyUnit Nil)
termBuilder ast
  = do R _ TyUnit res term <- build Nil ast
         | R _ ty _ _ => throw (NotSupposedToHappen Nothing) -- @TODO fix
       case res of
         Nil => pure term
         _ => throw (NotSupposedToHappen Nothing)


-- [ EOF ]
