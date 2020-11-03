module Language.SystemVerilog.Micro.Properties

import Data.Vect
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Toolkit.Data.Vect.Extra

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Direction
import Language.SystemVerilog.Micro

%access export
%default covering

total
Term : Context -> Ty -> Type
Term local type = Expr local Nil type

-- ------------------------------------------------------------------ [ Weaken ]

total
weaken : (shunt : Index orig (n, a) -> Index new (n,a))
      -> (Index ((n',b)::orig) (n,a) -> Index ((n',b)::new) (n,a))
weaken shunt First = First
weaken shunt (Next x) = Next (shunt x)

-- ------------------------------------------------------------------ [ Rename ]

total
map : (f : {a : ty} -> n a -> m a)
    -> DList ty n as
    -> DList ty m as
map f Nil = []
map f (head :: tail) = f head :: map f tail

covering
rename : (shunt : {a : Ty} -> {l : String} -> Index orig (l,a) -> Index new (l,a))
      -> ({a : Ty} -> Term orig a -> Term new a)
rename shunt End = End
rename shunt (Local l idx) = Local l (shunt idx)
rename shunt (Global l idx) = Global l idx
rename shunt (Let this beThis withType prf inThis)
  = Let this
        (rename shunt beThis)
        (rename shunt withType)
        prf
        (rename (weaken shunt) inThis)
rename shunt (Seq this that) = Seq (rename shunt this) (rename shunt that)
rename shunt TYPE = TYPE
rename shunt DataLogic = DataLogic
rename shunt DataNet = DataNet
rename shunt (DataArray type size)
  = DataArray (rename shunt type) size
rename shunt (DataStruct xs)
  = DataStruct (map (\(k,v) => MkPair k (rename shunt v)) xs)

rename shunt (DataUnion xs)
  = DataUnion (map (\(k,v) => MkPair k (rename shunt v)) xs)
rename shunt (Port l d type) = Port l d (rename shunt type)
rename shunt (MDecl ports) {orig} {new} = MDecl (map (\v => rename shunt v) ports)

rename shunt NewChan = NewChan
rename shunt (NewModule ps) = NewModule (map (\(k,v) => MkPair k (rename shunt v)) ps)

-- ----------------------------------------------------------------- [ Weakens ]

covering
weakens : (shunt : Index orig (n,a) -> Term new a)
       -> (Index ((n',b)::orig) (n,a) -> Term ((n',b)::new) a)
weakens shunt (First) = Local _ First
weakens shunt (Next rest) = rename Next (shunt rest)

-- ---------------------------------------------------- [ General Substitution ]

covering
substitute : (shunt : {a : Ty} -> {l : String} -> Index orig (l,a) -> Term new a)
          -> ({a : Ty} -> Term orig a -> Term new a)
substitute _ End = End
substitute shunt (Local l idx) = shunt idx
substitute _ (Global l idx) = Global l idx
substitute shunt (Let this beThis withType prf inThis)
  = Let this
        (substitute shunt beThis)
        (substitute shunt withType)
        prf
        (substitute (weakens shunt) inThis)
substitute shunt (Seq this thenThat)
  = (substitute shunt this) `Seq` (substitute shunt thenThat)
substitute _ TYPE = TYPE
substitute _ DataLogic = DataLogic
substitute _ DataNet = DataNet
substitute shunt (DataArray type size)
  = DataArray (substitute shunt type) size
substitute shunt (DataStruct kvs)
  = DataStruct $ map (\(MkPair k v) => MkPair k (substitute shunt v)) kvs
substitute shunt (DataUnion kvs)
  = DataUnion $ map (\(MkPair k v) => MkPair k (substitute shunt v)) kvs
substitute shunt (Port l d type) = Port l d (substitute shunt type)
substitute shunt (MDecl ports) {orig} {new} = MDecl (map (\p => substitute shunt p) ports)

substitute _ NewChan = NewChan
substitute shunt (NewModule ps)
  = NewModule (map (\(MkPair k v) => MkPair k (substitute shunt v)) ps)

-- ----------------------------------------------------- [ Single Substitution ]

covering
subst : (this : Term orig b)
     -> (inThis : Term ((l,b) :: orig) a)
     -> Term orig a
subst {orig} {l} {b} {a} this inThis = substitute map inThis
  where
    total
    map : {a : Ty}
       -> {n : String}
       -> Index ((l,b)::orig) (n, a)
       -> Term orig a
    map First = this
    map (Next x) = Local _ x

-- ------------------------------------------------------------------ [ Values ]

data ValueKV : (value : Term g a -> Type)
            -> (String, Term g a)
            -> Type
  where
    KVIsValue : (prf : value v)
             -> ValueKV value (k,v)

data Value : Term g type -> Type where
  EndV : Value End

  TypeV : Value TYPE

  DataLogicV : Value DataLogic
  DataNetV : Value DataNet

  DataArrayV : (prf : Value type) -> Value (DataArray type size)

  DataStructV : {kvs : Vect (S n) (Pair String (Term Nil DATA))}
             -> (prf : DVect (Pair String (Term Nil DATA)) (ValueKV Value) (S n) kvs)
             -> Value (DataStruct kvs)

  DataUnionV : {kvs : Vect (S n) (Pair String (Term Nil DATA))}
            -> (prf : DVect (Pair String (Term Nil DATA)) (ValueKV Value) (S n) kvs)
            -> Value (DataUnion kvs)

  PortV : (prf : Value type)
       -> Value (Port l d type)

  NewChanV : Value NewChan

  NewModuleV : (kvsV : DList (Pair String (Term Nil CHAN)) (ValueKV Value) kvs)
            -> Value (NewModule kvs)

  SeqV : (thisV : Value this)
      -> (thatV : Value that)
      -> Value (Seq this that)


-- ---------------------------------------------------- [ Small Step Reduction ]

data ReduxKVsModule : (redux : Term g CHAN -> Term g CHAN -> Type)
                   -> List (String, Term g CHAN)
                   -> List (String, Term g CHAN)
                   -> Type
  where
    EmptyKVM  : ReduxKVsModule redux Nil Nil

    ExtendKVMV : (prf : Value this)
              -> (rest : ReduxKVsModule redux thisRest thatRest)
              -> ReduxKVsModule redux ((k,this)::thisRest)
                                      ((k,this)::thatRest)

    ExtendKVMR : (prf : redux this that)
              -> (rest : ReduxKVsModule redux thisRest thatRest)
              -> ReduxKVsModule redux ((k,this)::thisRest)
                                      ((k,that)::thatRest)

data ReduxKVsData : (redux : Term g a -> Term g a -> Type)
                 -> Vect n (String, Term g a)
                 -> Vect n (String, Term g a)
                 -> Type
  where
    EmptyKVD  : ReduxKVsData redux Nil Nil

    ExtendKVDV : (prf : Value this)
              -> (rest : ReduxKVsData redux thisRest thatRest)
              -> ReduxKVsData redux ((k,this)::thisRest)
                                    ((k,this)::thatRest)

    ExtendKVDR : (prf : redux this that)
              -> (rest : ReduxKVsData redux thisRest thatRest)
              -> ReduxKVsData redux ((k,this)::thisRest)
                                    ((k,that)::thatRest)


data Redux : (this : Term g a)
          -> (that : Term g a)
          -> Type
  where
    LetTypeE : (prfR : Redux withType withType')
            -> Redux (Let this beThis withType  prf inThis)
                     (Let this beThis withType' prf inThis)
    LetBExprE : (prfType : Value withType)
             -> (prfR    : Redux beThis beThis')
            -> Redux (Let this beThis  withType prf inThis)
                     (Let this beThis' withType prf inThis)
    LetBodyB : (prfType  : Value withType)
            -> (prfBExpr : Value beThis)
           -> Redux (Let this beThis withType prf inThis)
                    (subst beThis inThis)

    SeqLeftE : (prf : Redux this this')
            -> Redux (Seq this  that)
                     (Seq this' that)
    SeqRightE : (prfThatV : Value this)
             -> (prf : Redux that that')
             -> Redux (Seq this that)
                      (Seq this that')

    DArrayE : (prf : Redux type type')
           -> Redux (DataArray type  size)
                    (DataArray type' size)

    DStructE : (prf : ReduxKVsData Redux kvs kvs')
            -> Redux (DataStruct kvs)
                     (DataStruct kvs')
    DUnionE : (prf : ReduxKVsData Redux kvs kvs')
            -> Redux (DataUnion kvs)
                     (DataUnion kvs')

    PortE : (prf : Redux this that)
         -> Redux (Port l d this)
                  (Port l d that)

    NewModuleE : (prf : ReduxKVsModule Redux kvs kvs')
              -> Redux (NewModule kvs) (NewModule kvs')


-- ---------------------------------------------------------------- [ Progress ]

data Normalisation : (this : Term g a)
                  -> (that : Term g a)
                  -> Type
  where
    Refl  : Normalisation t t
    Trans : Redux a b
         -> Normalisation b c
         -> Normalisation a c

data Progress : (Term Nil a) -> Type where
  Done : Value m -> Progress m
  Step : {n : Term Nil a}
      -> (prf : Redux m n)
      -> Progress m

covering
progress : (term : Term Nil type)
        -> Progress term
progress End {type = UNIT} = Done EndV

progress (Local _ First) {type = _} impossible
progress (Local _ (Next _)) {type = _} impossible
progress (Global _ First) {type = _} impossible
progress (Global _ (Next _)) {type = _} impossible

progress (Let this beThis withType prf inThis) {type = type} with (progress withType)
  progress (Let this beThis withType prf inThis) {type = type} | (Done x) with (progress beThis)
    progress (Let this beThis withType prf inThis) {type = type} | (Done x) | (Done y) = Step (LetBodyB x y)
    progress (Let this beThis withType prf inThis) {type = type} | (Done x) | (Step y) = Step (LetBExprE x y)

  progress (Let this beThis withType prf inThis) {type = type} | (Step x) = Step (LetTypeE x)


progress (Seq this that) {type = type} with (progress this)
  progress (Seq this that) {type = type} | (Done x) with (progress that)
    progress (Seq this that) {type = type} | (Done x) | (Done y) = Done (SeqV x y)
    progress (Seq this that) {type = type} | (Done x) | (Step prf) = Step (SeqRightE x prf)

  progress (Seq this that) {type = type} | (Step prf) = Step (SeqLeftE prf)

progress TYPE {type = TYPE} = Done TypeV
progress DataLogic {type = DATA} = Done DataLogicV
progress DataNet {type = DATA} = Done DataNetV
progress (DataArray x size) {type = DATA} with (progress x)
  progress (DataArray x size) {type = DATA} | (Done type') = Done (DataArrayV type')
  progress (DataArray x size) {type = DATA} | (Step prf) = Step (DArrayE prf)

progress (DataStruct xs) {type = DATA} = ?progress_rhs_10
progress (DataUnion xs) {type = DATA} = ?progress_rhs_11

progress (Port label dir x) {type = (PORT label)} with (progress x)
  progress (Port label dir x) {type = (PORT label)} | (Done y) = Done (PortV y)
  progress (Port label dir x) {type = (PORT label)} | (Step prf) = Step (PortE prf)

progress (MDecl ports) {type = (MODULE names)} = ?progress_rhs_13

progress NewChan {type = CHAN} = Done NewChanV
progress (NewModule xs) {type = (MINST names)} = ?progress_rhs_15

-- ------------------------------------------------------------ [ Preservation ]

-- no seperate proof required, the type-checker ensures it.
