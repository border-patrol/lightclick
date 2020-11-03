module LightClick.IR.Channel.MicroSV.Intermediate

import Data.List
import Data.Vect
import Data.Strings

import Data.Vect.Sort

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn
import Toolkit.Data.DVect

import LightClick.Error

import LightClick.Types.Direction

import LightClick.IR.ModuleCentric
import LightClick.IR.ChannelCentric
import LightClick.IR.Channel.MicroSV.InterpTy
import LightClick.IR.Channel.MicroSV.Error

import public Language.SystemVerilog.MetaTypes
import public Language.SystemVerilog.Direction

%default total

public export
data MicroSvIR : (lctxt : Context)
              -> (type : Ty)
              -> Type
  where
    End : MicroSvIR ctxt UNIT

    Local  : (label : String) -> Index ctxt (label, type) -> MicroSvIR ctxt type
    Global : (label : String) -> (ty : Ty) -> MicroSvIR ctxt ty

    Let : {typeE, ty : Ty}
       -> (this : String)
       -> (beThis : MicroSvIR ctxt typeE)
       -> (withType : MicroSvIR ctxt ty)
       -> (inThis : MicroSvIR ((this,typeE)::ctxt) typeB)
       -> MicroSvIR ctxt typeB

    Seq : {typeA, typeB : Ty}
       -> MicroSvIR ctxt typeA
       -> MicroSvIR ctxt typeB
       -> MicroSvIR ctxt typeB

    TYPE : MicroSvIR ctxt TYPE

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

    MDecl : DList String (\s => MicroSvIR ctxt (PORT s)) names
         -> MicroSvIR ctxt (MODULE names)

    -- Ctors
    NewChan : MicroSvIR ctxt CHAN
    NewModule : List (Pair String (MicroSvIR ctxt CHAN))
             -> MicroSvIR ctxt (MINST names)

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

TFuncSig : (local : Context) -> TyIR -> Type
TFuncSig local type =
      (env  : TEnv local)
   -> (expr : ChannelIR type)
   -> Either TError (TRes local type)


%inline
port : (f : TFuncSig local PORT)
    -> (e : TEnv local)
    -> (p : ChannelIR PORT)
    -> Either TError (s ** MicroSvIR local (PORT s))
port f e p with (f e p)
  port f e p | (Left l) = Left l
  port f e p | (Right (MkTRes decls (Port l dir type) (PP l))) = Right (_ ** Port l dir type)
  port f e p | (Right (MkTRes decls _                 (PP l))) = Left (General $ "Port Expected")

ports' : (f  : TFuncSig local PORT)
      -> (e  : TEnv local)
      -> (ps : Vect n (ChannelIR PORT))
      -> Either TError (ns ** DList String (\s => MicroSvIR local (PORT s)) ns)
ports' f e [] = pure (_ ** Nil)
ports' f e (x :: xs) =
  do x' <- port f e x
     xs' <- ports' f e xs
     pure (_ ** (snd x') :: (snd xs'))

ports : (f  : TFuncSig local PORT)
     -> (e  : TEnv local)
     -> (ps : Vect (S n) (ChannelIR PORT))
     -> Either TError (ns ** DList String (\s => MicroSvIR local (PORT s)) ns)
ports f e (x :: xs) =
      do x' <- port f e x
         xs' <- ports' f e xs
         pure (_ ** (snd x') :: (snd xs'))

%inline
chan : (f : TFuncSig local CHAN)
    -> (e : TEnv local)
    -> (c : (String, ChannelIR CHAN))
    -> Either TError (String, MicroSvIR local CHAN)
chan f e (l,c) with (f e c)
  chan f e (l,c) | (Left err) = Left $ Nested "Attempted to convert chan" err
  chan f e (l,c) | (Right (MkTRes decls expr CC)) = Right (l,expr)

chans' : (f  : TFuncSig local CHAN)
      -> (e  : TEnv local)
      -> (cs : Vect n (String, ChannelIR CHAN))
      -> Either TError (List (String, (MicroSvIR local CHAN)))
chans' f e [] = pure Nil
chans' f e (x :: xs) =
  do x' <- chan f e x
     xs' <- chans' f e xs
     pure (x'::xs')


chans : (f  : TFuncSig local CHAN)
     -> (e  : TEnv local)
     -> (cs : Vect (S n) (String, ChannelIR CHAN))
     -> Either TError (List (String, (MicroSvIR local CHAN)))
chans f e (x :: xs) =
      do x' <- chan f e x
         xs' <- chans' f e xs
         pure (x'::xs')

%inline
kvpair : (f : TFuncSig local DATA)
      -> (e : TEnv local)
      -> (c : (String, ChannelIR DATA))
      -> Either TError (String, MicroSvIR local DATA)
kvpair f e (l,c) with (f e c)
  kvpair f e (l,c) | (Left err) = Left $ Nested "Attempted to convert KVPair" err
  kvpair f e (l,c) | (Right (MkTRes decls expr DD)) = Right (l,expr)

kvpairs' : (f  : TFuncSig local DATA)
        -> (e  : TEnv local)
        -> (cs : Vect n (String, ChannelIR DATA))
        -> Either TError (Vect n (String, (MicroSvIR local DATA)))
kvpairs' f e [] = pure Nil
kvpairs' f e (x :: xs) =
  do x' <- kvpair f e x
     xs' <- kvpairs' f e xs
     pure (x'::xs')

kvpairs : {n : Nat}
       -> (f  : TFuncSig local DATA)
       -> (e  : TEnv local)
       -> (cs : Vect (S n) (String, ChannelIR DATA))
       -> Either TError (Vect (S n) (String, (MicroSvIR local DATA)))
kvpairs f e (x :: xs) =
      do x' <- kvpair f e x
         xs' <- kvpairs' f e xs
         pure (x'::xs')


Eq (ChannelIR PORT) where
  (==) (CPort x f d) (CPort y g e) = x == y
  (==) _ _ = False

Ord (ChannelIR PORT) where
  compare (CPort x f d) (CPort y g e) = compare x y
  compare _ _ = LT


covering
convert : {type : TyIR}
       -> {local : Context}
       -> (e : TEnv local)
       -> (c : ChannelIR type)
       -> Either TError (TRes local type)
-- [ References ]
convert e (CRef x type) with (e)
  convert e (CRef x type) | (MkTEnv decls local) with (isIndex x local)
    convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) with (interpTy type ty)
      convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) | (Yes prf) =
        pure (MkTRes decls (Local x idx) prf)
      convert e (CRef x type) | (MkTEnv decls local) | (Yes (ty ** idx)) | (No contra) =
        Left $ General (unwords ["Attempting to construct Local", show x])

    convert e (CRef x type) | (MkTEnv decls local) | (No contra) with (lookup x decls)
      convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Nothing
        = Left $ General (unwords ["Attempting to construct global, identifier not found", show x])
      convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty with (interpTy type ty)
        convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty | (Yes prf)
          = pure (MkTRes decls (Global x ty) prf)
        convert e (CRef x type) | (MkTEnv decls local) | (No contra) | Just ty | (No contra')
          = Left $ General (unwords ["Attempting to construct Global type issue", show x])

-- [ NOTE ] traverse decls and extra ty to do proof. will formalise later.


-- [ Structural Statements ]

---- [ Let Bindings ]

---- Is `this` bindable and if so then how
convert e (CLet bind this {term} inThis) with (isBindable term)

  {- [ Translate the Global Bindings]

    - Extend global declarations with result, assume that the expr is closed
    - Translate `inThis`
  -}

  convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) with (e)
    convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) | (MkTEnv decls local) with (convert (MkTEnv decls Nil) this)
      convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) | (MkTEnv decls local) | (Left l)
        = Left $ Nested "Attempting to construct global declaration" l
      convert e (CLet bind this {term = term} inThis) | (IsDecl prfDecl) | (MkTEnv decls local) | (Right (MkTRes rest expr prf))
        = convert (MkTEnv (MkDecl bind expr::rest) local) inThis


  {- [ Translate the local bindings ]

    Convert the `this` and `inThis` before constructing the type of `this`.
  -}
  convert e (CLet bind this {term = term} inThis) | (IsLet x) with (e)
    convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local) with (convert (MkTEnv decls local) this)
      convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local) | (Left l)
        = Left $ Nested "Attempting to this of local let" l
      convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) with (Intermediate.convert (MkTEnv decls ((bind, getType expr)::local)) inThis)
        convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Left l) = Left $ Nested "Attempting to construct body of Local Let" l

        -- MicroSV is typed, we need to introspect `this` again because we need to get the type.
        convert e (CLet bind this {term = term} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) with (x)

          {- [ Translating Module instantiations ]

            When MINST
              - the type is the name/ref to the module
              - the value is the result of translating `this`
          -}
          convert e (CLet bind this {term = CONN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstM with (this)
            convert e (CLet bind this {term = CONN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstM | (CModuleInst mtype _) with (Intermediate.convert e mtype)
              convert e (CLet bind this {term = CONN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstM | (CModuleInst mtype _) | Left l
                = Left $ Nested "Cannot construct type for local let module" l
              convert e (CLet bind this {term = CONN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstM | (CModuleInst mtype _) | Right (MkTRes _ newMType prfType)
                = pure (MkTRes y (Let bind expr newMType z) w)

            convert e (CLet bind this {term = CONN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstM | _
              = Left $ General "Expected local let `this` to be CModuleInst, it wasn't"

          {- [ Translating Channel terms ]

            When CHAN
              - the type is var or inline data type
              - the value is `NewChan`
          -}
          convert e (CLet bind this {term = CHAN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstC with (this)
            convert e (CLet bind this {term = CHAN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstC | (CChan dtype) with (convert e dtype)
              convert e (CLet bind this {term = CHAN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstC | (CChan dtype) | Left l
                = Left $ Nested "Attempting to construct this from local let chan" l
              convert e (CLet bind this {term = CHAN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstC | (CChan dtype) | (Right (MkTRes _ newDType prfType))
                = pure (MkTRes y (Let bind expr newDType z) w)

            convert e (CLet bind this {term = CHAN} inThis) | (IsLet x) | (MkTEnv decls local) | (Right (MkTRes rest expr prf)) | (Right (MkTRes y z w)) | IsInstC | _
              = Left $ General "Expected local let `this` to be CChan, it wasn't"

  -- Any other pattern here is unexpected.
  convert e (CLet bind this {term = term} inThis) | Unbindable = Left $ General "We were given something unbindable"


---- [ Sequencing ]
convert (MkTEnv decls local) (CSeq x y) with (convert (MkTEnv decls local) x)
  convert (MkTEnv decls local) (CSeq x y) | Left err = Left $ Nested "Left Sequent failed" err
  convert (MkTEnv decls local) (CSeq x y) | Right (MkTRes declsX x' prfX) with (convert (MkTEnv declsX local) y)
    convert (MkTEnv decls local) (CSeq x y) | Right (MkTRes declsX x' prfX) | Left err
      = Left $ Nested "Right  sequant failed" err
    convert (MkTEnv decls local) (CSeq x y) | Right (MkTRes declsX x' prfX) | Right (MkTRes declsY y' prfY) =
      pure (MkTRes declsY (Seq x' y') prfY)

---- [ This is the End ]
convert e CEnd with (e)
  convert e CEnd | (MkTEnv decls local) = pure (MkTRes decls End UU)

-- [ Module Declarations ]

convert e (CPort l d type) with (convert e type)
  convert e (CPort l d type) | Left err
    = Left $ Nested "Attempting to construct type for Port" err
  convert e (CPort l d type) | (Right (MkTRes decls t' DD))
    = pure (MkTRes decls (Port l (interpDir d) t') (PP l))

convert e (CModule {n} xs) with (ports convert e (sort xs))
  convert e (CModule {n} xs) | (Left l)
    = Left $ Nested "Attempting to construct ports for Module Declaration" l
  convert e (CModule {n} xs) | (Right (ns ** ps)) with (e)
    convert e (CModule {n} xs) | (Right (ns ** ps)) | (MkTEnv decls local)
      = pure (MkTRes decls (MDecl ps) (MM ns))


-- [ Data Declarations ]

convert (MkTEnv decls local) CDataLogic = pure (MkTRes decls DataLogic DD)

convert e (CDataArray type k) with (convert e type)
  convert e (CDataArray type k) | Left l
    = Left $ Nested "Attempting to construct Data Type for array" l
  convert e (CDataArray type k) | Right res with (res)
    convert e (CDataArray type k) | Right res | (MkTRes decls type' DD)
      = pure (MkTRes decls (DataArray type' k) DD)

convert e (CDataStruct xs) with (e)
  convert e (CDataStruct xs) | (MkTEnv decls local)
    = do xs' <- kvpairs convert e xs
         pure (MkTRes decls (DataStruct xs') DD)

convert e (CDataUnion xs) with (e)
  convert e (CDataUnion xs) | (MkTEnv decls local)
    = do xs' <- kvpairs convert e xs
         pure (MkTRes decls (DataUnion xs') DD)


-- [ A Thing that should not exist in 'Our Normal Form' ]

convert e (CIDX label x y)
  = Left $ Nested "IDX Not expected" MalformedExpr

-- [ Constructors for Channels and Modules ]
convert e (CChan _) with (e)
  convert e (CChan _) | (MkTEnv decls local)
    = pure $ MkTRes decls NewChan CC

convert e (CModuleInst _ kvs) with (e)
  convert e (CModuleInst _ kvs) | (MkTEnv decls local)
    = do xs' <- chans convert e kvs
         let ns = map fst xs'
         pure (MkTRes decls (NewModule xs') (CM (sort ns)))


export
covering
runConvert : (c : ChannelIR UNIT)
               -> Either TError MicroSvIrSpec
runConvert expr with (convert (MkTEnv Nil Nil) expr)
  runConvert expr | Left l
    = Left $ Nested "Cannot consruct spec" l
  runConvert expr | Right (MkTRes decls expr' UU)
    = Right (MkMSVIRSpec decls expr')


-- --------------------------------------------------------------------- [ EOF ]
