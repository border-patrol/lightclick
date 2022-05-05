||| Convert the IR MicroSV to MicroSV itself.
|||
||| Module    : MicroSV.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
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

-- [ Helper Structures ]

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

  -- [ Helper Functions ]

  decl : {type   : Ty}
      -> {global : Context}
      -> (decls  : Micro.Decls global)
      -> (bind   : String)
      -> (expr   : MicroSvIR Nil type)
                -> LightClick ( ValidDecl type TYPE
                              , Expr Nil global type)

  decl decls bind e {type} {global} with (validDecl type TYPE)
    decl decls bind e {type = type} {global = global} | (Yes prf)
      = do d <- expr (MkEnv global decls Nil) e
           pure (prf,d)

    decl decls bind e {type = type} {global = global} | (No contra)
      = throw (MicroSVError MalformedExpr)

  decls : (ds : Intermediate.Decls types)
             -> LightClick (global ** ( ValidDecls types global
                                      , Decls global))
  decls []
    = pure (_ ** MkPair Empty Empty)

  decls ((MkDecl b e) :: rest)
    = do (ctxt ** MkPair ps ds) <- decls rest
         (p,d) <- decl ds b e
         pure (_ ** MkPair (Extend b p ps) (DeclAdd b d p ds))

  datatypes : (env : TEnv local global)
           -> (ds  : Vect n (String, MicroSvIR local DATA))
                  -> LightClick (Vect n (String, Expr local global DATA))

  datatypes env
    = traverse (\(l,e) => do {e' <- expr env e; pure (l,e')})

  ports : (env : TEnv local global)
       -> (ps  : DList String (\a => MicroSvIR local (PORT a)) names)
              -> LightClick (DList String (\s => Expr local global (PORT s)) names)
  ports env Nil
    = pure Nil

  ports env (p::ps)
    = do p' <- expr env p
         ps' <- ports env ps
         pure (p'::ps')

  chans : (env : TEnv local global)
       -> (cs  : DList String (\s => Pair (Label s) (MicroSvIR local CHAN)) names)
              -> LightClick (DList String
                                   (\s => Pair (Label s)
                                               (Expr local global CHAN))
                                   names)

  chans env []
    = pure Nil

  chans env ((L s, x) :: xs)
    = do x <- expr env x
         xs <- chans env xs
         pure ((L s, x) :: xs)

  ||| Expr to expressions.
  expr : (env  : TEnv local global)
         -> (expr : MicroSvIR local type)
                 -> LightClick (Expr local global type)
  expr env End
    = pure End

  expr env (Local label x)
    = pure (Local label x)

  expr env (Global label type) with (env)
    expr env (Global label type) | (MkEnv global decls local) with (isElem (label,type) global)
      expr env (Global label type) | (MkEnv global decls local) | (Yes prf)
        = pure (Global label prf)

      expr env (Global label type) | (MkEnv global decls local) | (No contra)
        = throw (MicroSVError (General $ unwords ["Attempting to generate Global ref failed:", show label]))

  -- [ Structural Statements ]

  expr env (Let this beThis {typeE} withType {ty} inThis) with (validLet typeE ty)
    expr (MkEnv global decls local) (Let this beThis {typeE = typeE} withType {ty = ty} inThis) | (Yes prf)
      = do e <- expr (MkEnv global decls local) beThis
           t <- expr (MkEnv global decls local) withType
           b <- expr (MkEnv global decls ((this,typeE)::local)) inThis
           pure (Let this e t prf b)

    expr env (Let this beThis {typeE = typeE} withType {ty = ty} inThis) | (No contra)
      = throw (MicroSVError (General $ unwords ["Invalid Let:", show typeE, show ty]))

  expr env (Seq x y)
    = do x' <- expr env x
         y' <- expr env y
         pure (Seq x' y')

  -- [ Types]

  expr env TYPE
    = pure TYPE

  expr env GATE
    = pure GATE

  -- [ Data types ]
  expr env DataLogic
    = pure DataLogic

  expr env (DataEnum xs)
    = pure (DataEnum xs)

  expr env (DataArray x size)
    = do t <- expr env x
         pure (DataArray t size)

  expr env (DataStruct xs)
    = do xs' <- datatypes env xs
         pure (DataStruct xs')

  expr env (DataUnion xs)
    = do xs' <- datatypes env xs
         pure (DataUnion xs')

  -- [ Module constructors ]
  expr env (Port label dir x)
    = pure (Port label dir !(expr env x))

  expr env (MDecl x)
    = pure (MDecl !(ports env x))

  -- [ Value Constructors ]
  expr env NewChan
    = pure NewChan

  expr env NoOp
    = pure NoOp

  expr env (NewModule xs)
    = pure (NewModule !(chans env xs))

  -- [ Gates ]
  expr env (Not o i)
    = pure (Not !(expr env o) !(expr env i))

  expr env (Gate x out ins)
    = do o <- expr env out
         i <- traverse (expr env) ins
         pure (Gate x o i)

||| Run conversion from MicroSVIR to SystemVerilog
export
covering
systemVerilog : (spec : MicroSvIrSpec)
                     -> LightClick Spec
systemVerilog (MkMSVIRSpec ds top)
  = do (g ** (pDs,ds)) <- decls ds
       t <- expr (MkEnv g ds Nil) top
       pure (MkSpec ds t)

-- [ EOF ]
