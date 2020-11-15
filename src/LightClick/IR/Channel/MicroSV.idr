module LightClick.IR.Channel.MicroSV

import Data.List
import Data.Vect
import Data.Strings

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.DList.DeBruijn

import LightClick.Error

import LightClick.Types.Direction

import LightClick.IR.ModuleCentric

import LightClick.IR.Channel.MicroSV.InterpTy
import LightClick.IR.Channel.MicroSV.Error
import LightClick.IR.Channel.MicroSV.Intermediate

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Micro

%default covering

data TEnv : (local,global : Context) -> Type where
     MkEnv : (global : Context)
          -> (decls : Decls global)
          -> (local : Context)
          -> TEnv local global


ConvertFuncSig : (local, global : Context) -> Ty -> Type
ConvertFuncSig local global type =
     (env : TEnv local global)
  -> (expr : MicroSvIR local type)
  -> Either TError (Expr local global type)

convertExpr :  (env : TEnv local global)
  -> (expr : MicroSvIR local type)
  -> Either TError (Expr local global type)

convertDecl : {type : Ty}
           -> {global : Context}
           -> (decls : Micro.Decls global)
           -> (bind  : String)
           -> (expr  : MicroSvIR Nil type)
           -> Either TError (ValidDecl type TYPE, Expr Nil global type)
convertDecl decls bind expr {type} {global} with (validDecl type TYPE)
  convertDecl decls bind expr {global} | (Yes prfVDecl) with (convertExpr (MkEnv global decls Nil) expr)
    convertDecl decls bind expr {global} | (Yes prfVDecl) | (Left l) = Left $ Nested "Converting Decl" l
    convertDecl decls bind expr {global} | (Yes prfVDecl) | (Right newDecl) = Right (prfVDecl, newDecl)

  convertDecl decls bind expr | (No contra) = Left MalformedExpr


data ValidDecls : List Ty
               -> Context
               -> Type
  where
    Empty : ValidDecls Nil Nil
    Extend : (name : String)
          -> (prf  : ValidDecl type TYPE)
          -> (rest : ValidDecls types kvs)
          -> ValidDecls (type::types) ((name,type)::kvs)

convertDecls : (decls : Intermediate.Decls types)
            -> Either TError (global ** (ValidDecls types global, Decls global))

convertDecls [] = Right (_ ** (Empty, Empty))

convertDecls (MkDecl binder expr :: rest) with (convertDecls rest)
  convertDecls (MkDecl binder expr :: rest) | Left l
    = Left $ Nested "Converting Decls" l

  convertDecls (MkDecl binder expr :: rest) | Right (ctxt ** MkPair ps ds) with (convertDecl ds binder expr)

    convertDecls (MkDecl binder expr :: rest) | Right (ctxt ** MkPair ps ds) | (Left l)
      = Left l

    convertDecls (MkDecl binder expr :: rest) | Right (ctxt ** MkPair ps ds) | (Right (p,d))
      = Right (_ ** MkPair (Extend binder p ps) (DeclAdd binder d p ds))


convertData : {n : Nat} -> (f : ConvertFuncSig local global a)
           -> (env : TEnv local global)
           -> (ds : Vect (S n) (Pair String (MicroSvIR local a)))
           -> Either TError (Vect (S n) (Pair String (Expr local global a)))

convertData {n=n} f env ((k,v) :: xs) with (xs)
  convertData {n=Z} f env ((k,v) :: xs) | []
    = do r <- f env v
         pure [(k,r)]

  convertData {n=S n}f env ((k,v) :: xs) | (y :: ys)
    = do r <- (f env v)
         ys' <- convertData f env (y::ys)
         pure $ (k,r) :: ys'

convertPorts : (env : TEnv local global)
            -> (ports : DList String (\a => MicroSvIR local (PORT a)) names)
            -> Either TError (DList String (\s => Expr local global (PORT s)) names)

convertPorts env Nil = Right Nil

convertPorts env (elem :: rest)
  = do r <- convertExpr env elem
       rs <- convertPorts env rest
       pure (r::rs)

convertChans : (f : ConvertFuncSig local global CHAN)
            -> (env : TEnv local global)
            -> (ds : List (Pair String (MicroSvIR local CHAN)))
            -> Either TError (List (Pair String (Expr local global CHAN)))

convertChans _ _ Nil = Right Nil

convertChans f env ((k,v) :: xs) with (xs)
  convertChans f env ((k,v) :: xs) | []
    = do r <- f env v
         pure [(k,r)]

  convertChans f env ((k,v) :: xs) | (y :: ys)
    = do r <- f env v
         ys' <- convertChans f env (y::ys)
         pure $ (k,r) :: ys'



-- [ Implementation of `convertExpr` ]
convertExpr env End = pure End

convertExpr env (Local label x) = pure $ Local label x

convertExpr env (Global label ty) with (env)
  convertExpr env (Global label ty) | (MkEnv global decls local) with (isElem (label,ty) global)
    convertExpr env (Global label ty) | (MkEnv global decls local) | (Yes idx)
      = pure (Global label idx)
    convertExpr env (Global label ty) | (MkEnv global decls local) | (No contra)
      = Left $ General $ unwords ["Attempting to generate Global ref failed:", show label]

-- [ Structural Statements ]
convertExpr env (Let this beThis {typeE} withType {ty} inThis) with (validLet typeE ty)
  convertExpr env (Let this beThis {typeE} withType {ty} inThis) | Yes prf with (env)
    convertExpr env (Let this beThis {typeE} withType {ty} inThis) | Yes prf | MkEnv global decls local
      = do beThis' <- convertExpr (MkEnv global decls local) beThis
           withType' <- convertExpr (MkEnv global decls local) withType
           inThis' <- convertExpr (MkEnv global decls ((this,typeE)::local)) inThis
           pure (Let this beThis' withType' prf inThis')

  convertExpr env (Let this beThis {typeE} withType {ty} inThis) | No x
    = Left $ General $ unwords ["Invalid Let:", show typeE, show ty]

convertExpr env (Seq x y) with (convertExpr env x)
  convertExpr env (Seq x y) | Left err = Left err

  convertExpr env (Seq x y) | Right x' with (convertExpr env y)
    convertExpr env (Seq x y) | Right x' | Left err
      = Left err
    convertExpr env (Seq x y) | Right x' | Right y'
      = pure (Seq x' y')

-- [ The TYPE ]
convertExpr env TYPE = pure TYPE

-- [ The GATE ]
convertExpr env GATE = pure GATE

-- [ Data types ]
convertExpr env DataLogic = pure DataLogic
convertExpr env (DataArray type size)
  = do type' <- convertExpr env type
       pure (DataArray type' size)

convertExpr env (DataStruct xs)
  = do xs' <- convertData convertExpr env xs
       pure (DataStruct xs')

convertExpr env (DataUnion xs)
  = do xs' <- convertData convertExpr env xs
       pure (DataUnion xs')

-- [ Module constructors ]
convertExpr env (Port label dir type)
  = do type' <- convertExpr env type
       pure (Port label dir type')

convertExpr env (MDecl ports)
  = do ps <- convertPorts env ports
       pure (MDecl ps)

-- [ Value Constructors ]
convertExpr env NewChan = pure NewChan

convertExpr env (NewModule xs)
  = do xs' <- convertChans convertExpr env xs
       pure (NewModule xs')

-- [ Gates ]
convertExpr env (Not o i)
  = do o' <- convertExpr env o
       i' <- convertExpr env i
       pure (Not o' i')

convertExpr env (Gate ty o ins)
  = do o' <- convertExpr env o
       ins' <- traverse (convertExpr env) ins
       pure (Gate ty o' ins')


export
covering
convertSpec : (expr : MicroSvIrSpec)
                   -> Either TError Spec
convertSpec (MkMSVIRSpec decls expr) with (convertDecls decls)
  convertSpec (MkMSVIRSpec decls expr) | (Left l)
    = Left $ Nested "Attempting to build decls" l

  convertSpec (MkMSVIRSpec decls expr) | (Right (gs ** (prfVDecls,decls'))) with (convertExpr (MkEnv gs decls' Nil) expr)

    convertSpec (MkMSVIRSpec decls expr) | (Right (gs ** (prfVDecls,decls'))) | (Left l)
      = Left $ Nested "Attempted to build Spec" l

    convertSpec (MkMSVIRSpec decls expr) | (Right (gs ** (prfVDecls,decls'))) | (Right r)
      = pure (MkSpec decls' r)



-- --------------------------------------------------------------------- [ EOF ]
