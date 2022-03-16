module LightClick.IR.Channel.MicroSV

import Data.List
import Data.Vect
import Data.String

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.DList.DeBruijn

import LightClick.Core
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

data ValidDecls : List Ty
               -> Context
               -> Type
  where
    Empty : ValidDecls Nil Nil
    Extend : (name : String)
          -> (prf  : ValidDecl type TYPE)
          -> (rest : ValidDecls types kvs)
          -> ValidDecls (type::types) ((name,type)::kvs)

mutual
  decl : {type   : Ty}
      -> {global : Context}
      -> (decls  : Micro.Decls global)
      -> (bind   : String)
      -> (expr   : MicroSvIR Nil type)
                -> LightClick (ValidDecl type TYPE, Expr Nil global type)
  decl decls bind expr {type} {global} with (validDecl type TYPE)
    decl decls bind expr {type = type} {global = global} | (Yes prf)
      = do d <- convert (MkEnv global decls Nil) expr
           pure (prf,d)

    decl decls bind expr {type = type} {global = global} | (No contra)
      = throw (MicroSVError MalformedExpr)

  decls : (ds : Intermediate.Decls types)
             -> LightClick (global ** (ValidDecls types global, Decls global))
  decls []
    = pure (_ ** MkPair Empty Empty)

  decls ((MkDecl b e) :: rest)
    = do (ctxt ** MkPair ps ds) <- decls rest
         (p,d) <- decl ds b e
         pure (_ ** MkPair (Extend b p ps) (DeclAdd b d p ds))

  datatypes : (env : TEnv local global)
           -> (ds  : Vect n (String, MicroSvIR local DATA))
                 -> LightClick (Vect n (String, Expr local global DATA))
  datatypes env = traverse (\(l,e) => do {e' <- convert env e; pure (l,e')})

  ports : (env : TEnv local global)
       -> (ps  : DList String (\a => MicroSvIR local (PORT a)) names)
              -> LightClick (DList String (\s => Expr local global (PORT s)) names)
  ports env Nil
    = pure Nil

  ports env (p::ps)
    = do p' <- convert env p
         ps' <- ports env ps
         pure (p'::ps')

  chans : (env : TEnv local global)
       -> (cs  : List (Pair String (MicroSvIR local CHAN)))
              -> LightClick (List (Pair String (Expr local global CHAN)))

  chans env = traverse (\(l,e) => do {e' <- convert env e; pure (l,e')})

  convert : (env  : TEnv local global)
         -> (expr : MicroSvIR local type)
                 -> LightClick (Expr local global type)
  convert env End
    = pure End

  convert env (Local label x)
    = pure (Local label x)

  convert env (Global label type) with (env)
    convert env (Global label type) | (MkEnv global decls local) with (isElem (label,type) global)
      convert env (Global label type) | (MkEnv global decls local) | (Yes prf)
        = pure (Global label prf)

      convert env (Global label type) | (MkEnv global decls local) | (No contra)
        = throw (MicroSVError (General $ unwords ["Attempting to generate Global ref failed:", show label]))

  -- [ Structural Statements ]

  convert env (Let this beThis {typeE} withType {ty} inThis) with (validLet typeE ty)
    convert (MkEnv global decls local) (Let this beThis {typeE = typeE} withType {ty = ty} inThis) | (Yes prf)
      = do e <- convert (MkEnv global decls local) beThis
           t <- convert (MkEnv global decls local) withType
           b <- convert (MkEnv global decls ((this,typeE)::local)) inThis
           pure (Let this e t prf b)

    convert env (Let this beThis {typeE = typeE} withType {ty = ty} inThis) | (No contra)
      = throw (MicroSVError (General $ unwords ["Invalid Let:", show typeE, show ty]))

  convert env (Seq x y)
    = do x' <- convert env x
         y' <- convert env y
         pure (Seq x' y')

  -- [ Types]

  convert env TYPE = pure TYPE
  convert env GATE = pure GATE

  -- [ Data types ]
  convert env DataLogic
    = pure DataLogic

  convert env (DataArray x size)
    = do t <- convert env x
         pure (DataArray t size)

  convert env (DataStruct xs)
    = do xs' <- datatypes env xs
         pure (DataStruct xs')

  convert env (DataUnion xs)
    = do xs' <- datatypes env xs
         pure (DataUnion xs')

  -- [ Module constructors ]
  convert env (Port label dir x)
    = pure (Port label dir !(convert env x))

  convert env (MDecl x)
    = pure (MDecl !(ports env x))

  -- [ Value Constructors ]
  convert env NewChan
    = pure NewChan

  convert env (NewModule xs)
    = pure (NewModule !(chans env xs))

  -- [ Gates ]
  convert env (Not o i)
    = pure (Not !(convert env o) !(convert env i))

  convert env (Gate x out ins)
    = do o <- convert env out
         i <- traverse (convert env) ins
         pure (Gate x o i)


export
covering
systemVerilog : (spec : MicroSvIrSpec) -> LightClick Spec
systemVerilog (MkMSVIRSpec ds top)
  = do (g ** (pDs,ds)) <- decls ds
       t <- convert (MkEnv g ds Nil) top
       pure (MkSpec ds t)

-- --------------------------------------------------------------------- [ EOF ]
