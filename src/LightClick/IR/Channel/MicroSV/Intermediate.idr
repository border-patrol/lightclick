module LightClick.IR.Channel.MicroSV.Intermediate

import Data.List
import Data.Vect
import Data.String

import Data.Vect.Sort

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn
import Toolkit.Data.DVect

import public Language.SystemVerilog.MetaTypes
import public Language.SystemVerilog.Gates
import public Language.SystemVerilog.Direction

import LightClick.Error
import LightClick.Core

import LightClick.Types.Direction

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric
import LightClick.IR.Channel.MicroSV.InterpTy
import LightClick.IR.Channel.MicroSV.Error

%default covering

public export
data MicroSvIR : (lctxt : Context)
              -> (type : Ty)
              -> Type
  where
    End : MicroSvIR ctxt UNIT

    Local  : (label : String)
                   -> Index ctxt (label, type)
                   -> MicroSvIR ctxt type

    Global : (label : String)
          -> (ty    : Ty)
                   -> MicroSvIR ctxt ty

    Let : {typeE, ty : Ty}
       -> (this     : String)
       -> (beThis   : MicroSvIR ctxt typeE)
       -> (withType : MicroSvIR ctxt ty)
       -> (inThis   : MicroSvIR ((this,typeE)::ctxt) typeB)
       -> MicroSvIR ctxt typeB

    Seq : {typeA, typeB : Ty}
       -> MicroSvIR ctxt typeA
       -> MicroSvIR ctxt typeB
       -> MicroSvIR ctxt typeB

    TYPE : MicroSvIR ctxt TYPE
    GATE : MicroSvIR ctxt GATE

    -- Decls
    DataLogic : MicroSvIR ctxt DATA

    DataArray : (type : MicroSvIR ctxt DATA) -> (size : Nat) -> MicroSvIR ctxt DATA

    DataStruct : {n : Nat} -> (xs : Vect (S n) (Pair String (MicroSvIR ctxt DATA)))
              -> MicroSvIR ctxt DATA

    DataUnion : {n : Nat} -> (xs : Vect (S n) (Pair String (MicroSvIR ctxt DATA)))
             -> MicroSvIR ctxt DATA

    Port : (label : String)
        -> (dir   : SystemVerilog.Direction.Direction)
        -> (type  : MicroSvIR ctxt DATA)
        -> MicroSvIR ctxt (PORT label)

    MDecl : DList String (MicroSvIR ctxt . PORT) names
         -> MicroSvIR ctxt (MODULE names)

    -- Ctors
    NoOp    : MicroSvIR ctxt CHAN
    NewChan : MicroSvIR ctxt CHAN
    NewModule : DList String (\s => Pair (Label s) (MicroSvIR ctxt CHAN)) names
             -> MicroSvIR ctxt (MINST names)

    -- Gates
    Not : (out : MicroSvIR ctxt CHAN)
       -> (ins : MicroSvIR ctxt CHAN)
              -> MicroSvIR ctxt GINST

    Gate : {n    : Nat}
        -> (type : TyGateComb)
        -> (out  : MicroSvIR ctxt CHAN)
        -> (ins  : Vect (S (S n)) (MicroSvIR ctxt CHAN))
                -> MicroSvIR ctxt GINST


export
getType : {type : Ty} -> MicroSvIR ctxt type -> Ty
getType {type} _ = type

public export
data Decl : Ty -> Type where
  MkDecl : {type : Ty} -> String -> MicroSvIR Nil type -> Decl type

public export
Decls : List Ty -> Type
Decls = DList Ty Decl
-- Could turn into a triple/custom data type to collect proof that the `type` is valid for a declaration

export
lookup : String -> Decls ty -> Maybe Ty
lookup x [] = Nothing
lookup x (MkDecl y expr :: rest) with (decEq x y)
  lookup x (MkDecl x expr :: rest) | (Yes Refl) = Just $ getType expr
  lookup x (MkDecl y expr :: rest) | (No contra) = lookup x rest

public export
data MicroSvIrSpec : Type where
  MkMSVIRSpec : (decls : Decls types)
             -> (expr  : MicroSvIR Nil UNIT)
             -> MicroSvIrSpec


data TEnv : (local : context) -> Type where
  MkTEnv : {types : List Ty}
        -> (decls : Decls types)
        -> (local : Context)
        -> TEnv local

data TRes : (local : Context) -> (type : TyIR) -> Type where
  MkTRes : {type : Ty}
        -> {types : List Ty}
        -> {tyIR : TyIR}
        -> (decls : Decls types)
        -> (expr  : MicroSvIR ctxt type)
        -> (prf   : InterpTy tyIR type)
        -> TRes ctxt tyIR

Eq (ChannelIR PORT) where
  (==) (CPort x f n d) (CPort y g m e) = x == y
  (==) _ _ = False

Ord (ChannelIR PORT) where
  compare (CPort x f n d) (CPort y g m e) = compare x y
  compare _ _ = LT


mutual
  port : {local : _}
      -> (e : TEnv local)
      -> (p : ChannelIR PORT)
           -> LightClick (s ** MicroSvIR local (PORT s))
  port e p
    = do MkTRes decls (Port l dir type) (PP l) <- convert e p
             | MkTRes decls _ (PP l) => throw (MicroSVError (General "Port Expected"))
         pure (_ ** Port l dir type)

  ports : {local : _}
       -> (e  : TEnv local)
       -> (ps : Vect n (ChannelIR PORT))
             -> LightClick (ns ** DList String (\s => MicroSvIR local (PORT s)) ns)
  ports e []
    = pure (_ ** Nil)

  ports e (x :: xs)
      = do x'  <- port e x
           xs' <- ports e xs
           pure (_ ** snd x' :: snd xs')

  %inline
  chan : {local : _}
      -> (e : TEnv local)
      -> (c : (String, ChannelIR CHAN))
           -> LightClick (String, MicroSvIR local CHAN)
  chan e (l,c)
    = do MkTRes decls expr CC <- convert e c
         pure (l, expr)


  chans : {local : _}
       -> (e  : TEnv local)
       -> (cs : List (String, ChannelIR CHAN))
             -> LightClick (DPair (List String) (DList String (\s => Pair (Label s) (MicroSvIR local CHAN))))
  chans e []
    = pure (_ ** Nil)

  chans e (x :: xs)
    = do (s,x) <- chan e x
         (ss ** xs) <- chans e xs
         pure (s::ss ** (L s,x) :: xs)

  %inline
  chan' : {local : _}
       -> (e : TEnv local)
       -> (c : ChannelIR CHAN)
            -> LightClick (MicroSvIR local CHAN)
  chan' e c
    = do MkTRes decls expr CC <- convert e c
         pure expr

  chans' : {local : _}
        -> (e  : TEnv local)
        -> (cs : Vect n (ChannelIR CHAN))
              -> LightClick (Vect n (MicroSvIR local CHAN))
  chans' e = traverse (chan' e)

  %inline
  kvpair : {local : _}
        -> (e : TEnv local)
        -> (c : (String, ChannelIR DATA))
             -> LightClick (String, MicroSvIR local DATA)
  kvpair e (l,c)
    = do (MkTRes decls expr DD) <- convert e c
         pure (l,expr)

  kvpairs : {local : _}
         -> (e : TEnv local)
         -> (cs : Vect n (String, ChannelIR DATA))
               -> LightClick (Vect n (String, MicroSvIR local DATA))
  kvpairs e = traverse (kvpair e)

  convert : {type : TyIR}
         -> {local : Context}
         -> (e : TEnv local)
         -> (c : ChannelIR type)
              -> LightClick (TRes local type)

  -- [ References ]
  convert e (CRef x type) with (e)
    convert e (CRef x type) | (MkTEnv decls local) with (isIndex x local)
      convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) with (interpTy type ty)
        convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) | (Yes prf)
          = pure (MkTRes decls (Local x idx) prf)
        convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) | (No contra)
          = throw (MicroSVError (General (unwords ["Attempting to construct Local", show x])))

      convert e (CRef x type) | (MkTEnv decls local) | (No contra) with (lookup x decls)
        convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Nothing
          = throw (MicroSVError (General (unwords ["Attempting to construct global, identifier not found", show x])))
        convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty with (interpTy type ty)
          convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty | (Yes prf)
            = pure (MkTRes decls (Global x ty) prf)
          convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty | (No contra')
            = throw (MicroSVError (General (unwords ["Attempting to construct Global type issue", show x])))

  -- [ Structural Statements ]

  ---- [ Let Bindings ]

  ---- Is `this` bindable and if so then how
  convert e (CLet bind this {term} inThis) with (isBindable term)

    {- [ Translate the Global Bindings]

      - Extend global declarations with result, assume that the expr is closed
      - Translate `inThis`
    -}

    convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) with (e)
      convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) | (MkTEnv decls local)
        = do MkTRes rest expr prf <- convert (MkTEnv decls Nil) this
             convert (MkTEnv (MkDecl bind expr::rest) local) inThis


    {- [ Translate the local bindings ]

      Convert the `this` and `inThis` before constructing the type of `this`.
    -}
    convert e (CLet bind this {term = term} inThis) | (IsLet x) with (e)
      convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local)
        = do MkTRes rest expr prf <- convert (MkTEnv decls local) this
             MkTRes l' b pB <- convert (MkTEnv decls ((bind, getType expr) :: local)) inThis
             -- MicroSV is typed, we need to introspect `this` again because we need to get the type.
             case (x,this) of
               {- [ Translating Module instantiations ]

                 When MINST
                   - the type is the name/ref to the module
                   - the value is the result of translating `this`
               -}
               (IsInstM, (CModuleInst mtype _))
                 => do MkTRes _ newMType _ <- convert e mtype
                       pure (MkTRes l' (Let bind expr newMType b) pB)

               (IsInstM, _) => throw $ MicroSVError $ General "Expected local let `this` to be CModuleInst, it wasn't"

               {- [ Translating Channel terms ]

                 When CHAN
                   - the type is var or inline data type
                   - the value is `NewChan`
               -}


               (IsInstC, (CChan dtype))
                 => do MkTRes _ newDType _ <- convert e dtype
                       pure (MkTRes l' (Let bind expr newDType b) pB)

               (IsInstC, _) => throw $ MicroSVError $ General "Expected local let `this` to be CChan, it wasn't"

                {- [ Translating Gate terms ]

                  When GATE
                    - the type is var or inline data type
                    - the value is another gate.
                -}
               (IsInstG, (CNot o i))
                 => do MkTRes _ newNot _ <- convert e (CNot o i)
                       pure (MkTRes l' (Let bind expr GATE b) pB)

               (IsInstG, (CGate ty o ins))
                 => do MkTRes _ newNot _ <- convert e (CGate ty o ins)
                       pure (MkTRes l' (Let bind expr GATE b) pB)

               (IsInstG, _) => throw $ MicroSVError $ General "Expected local let `this` to be a Gate, it"

    -- Any other pattern here is unexpected.
    convert e (CLet bind this {term = term} inThis) | Unbindable
      = throw $ MicroSVError $ General "We were given something unbindable"


  ---- [ Sequencing ]
  convert (MkTEnv decls local) (CSeq x y)
    = do MkTRes dX x' pX <- convert (MkTEnv decls local) x
         MkTRes dY y' pY <- convert (MkTEnv dX    local) y
         pure (MkTRes dY (Seq x' y') pY)

  ---- [ This is the End ]
  convert e CEnd with (e)
    convert e CEnd | (MkTEnv decls local) = pure (MkTRes decls End UU)


  -- [ Module Declarations ]

  convert e (CPort l dir n type)
    = do MkTRes d t' DD <- convert e type
         pure (MkTRes d (Port l (interpDir dir) t') (PP l))

  convert (MkTEnv decls local) (CModule {n} xs)
    = do (ns ** ps) <- ports (MkTEnv decls local) (sort xs)
         pure (MkTRes decls (MDecl ps) (MM ns))

  -- [ Data Declarations ]

  convert (MkTEnv decls local) CDataLogic = pure (MkTRes decls DataLogic DD)

  convert e (CDataArray type k)
    = do MkTRes decls type' DD <- convert e type
         pure (MkTRes decls (DataArray type' k) DD)

  convert e (CDataStruct xs) with (e)
    convert e (CDataStruct xs) | (MkTEnv decls local)
      = do xs' <- kvpairs e xs
           pure (MkTRes decls (DataStruct xs') DD)

  convert e (CDataUnion xs) with (e)
    convert e (CDataUnion xs) | (MkTEnv decls local)
      = do xs' <- kvpairs e xs
           pure (MkTRes decls (DataUnion xs') DD)


  -- [ A Thing that should not exist in 'Our Normal Form' ]

  convert e (CIDX _ _)
    = throw $ MicroSVError $ Nested "IDX Not expected" MalformedExpr

  -- [ Constructors for Channels and Modules ]
  convert e (CChan _) with (e)
    convert e (CChan _) | (MkTEnv decls local)
      = pure $ MkTRes decls NewChan CC

  convert e (CModuleInst _ kvs) with (e)
    convert e (CModuleInst _ kvs) | (MkTEnv decls local)
        = do (ns ** kvs) <- chans e kvsSorted
             pure (MkTRes decls (NewModule kvs) (CM ns))
      where
        kvCompare : (x,y : (String, ChannelIR CHAN))
                        -> Ordering
        kvCompare x y = compare (fst x) (fst y)

        kvsSorted : List (String, ChannelIR CHAN)
        kvsSorted = sortBy kvCompare (toList kvs)

  -- [ Gates ]
  convert e (CNot o i) with (e)
    convert e (CNot o i) | (MkTEnv decls local)
      = do o' <- chan' e o
           i' <- chan' e i
           pure (MkTRes decls (Not o' i') GG)

  convert e (CGate ty o ins) with (e)
    convert e (CGate ty o ins) | (MkTEnv decls local)
      = do o'  <- chan' e o
           is' <- chans' e ins
           pure (MkTRes decls (Gate ty o' is') GG)

  convert (MkTEnv ds l) CNoOp = pure (MkTRes ds NoOp CC)

export
systemVerilog : (c : ChannelIR UNIT) -> LightClick MicroSvIrSpec
systemVerilog expr
  = do MkTRes ds e UU <- convert (MkTEnv Nil Nil) expr
       pure (MkMSVIRSpec ds e)

-- [ EOF ]
