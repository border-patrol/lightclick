||| Update global context during transformation.
|||
||| Module    : Update.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| A simple traversal over the terms in the specification to update
||| the global context.
|||
module LightClick.IR.Channel.MicroSV.Update

import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn

import LightClick.IR.ModuleCentric
import LightClick.IR.Channel.MicroSV.Error

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Micro

%default covering -- this file has caused the totality checker to hang.

public export
Update : Type -> Type
Update = Either TError

||| Run update over expressions.
export
update : (newGlobal : Context)
      -> (expr      : Expr local globalOld type)
                   -> Update (Expr local newGlobal type)

-- [ Helper Functions ]

updateKV : (newGlobal : Context)
        -> (fields    : (String, Expr local globalOld type))
                     -> Update (String, Expr local newGlobal type)
updateKV newGlobal (k,v)
  = do v' <- update newGlobal v
       pure (k,v')

updateKVs : (newGlobal : Context)
         -> (es        : Vect n (String, Expr local global type))
                       -> Update (Vect n (String, Expr local newGlobal type))
updateKVs newGlobal
  = traverse (updateKV newGlobal)

updatePorts : (newGlobal : Context)
           -> (es        : DList String (\s => Pair (Label s) (Expr l g CHAN)) names)
                        -> Update
                                  (DList String
                                         (\s => Pair (Label s) (Expr l newGlobal CHAN))
                                         names)
updatePorts newGlobal []
  = pure Nil

updatePorts newGlobal ((L s, x) :: xs)
  = do x <- update newGlobal x
       xs <- updatePorts newGlobal xs
       pure ((L s, x)::xs)

updateChans: (newGlobal : Context)
          -> (es        : Vect (S (S n)) (Expr local global type))
                       -> Update (Vect (S (S n)) (Expr local newGlobal type))
updateChans newGlobal
  = traverse (update newGlobal)

updateDecl : (newGlobal : Context)
          -> (expr      : Expr local globalOld (PORT s))
                       -> Update (Expr local newGlobal (PORT s))
updateDecl newGlobal
  = update newGlobal

updateMDecl : (newGlobal : Context)
           -> (ps        : DList String
                                 (\s => Expr lctxt gctxt (PORT s))
                                 names)
                        -> Update (DList String
                                  (\s => Expr lctxt newGlobal (PORT s))
                                  names)
updateMDecl newGlobal []
  = pure Nil
updateMDecl newGlobal (e :: rest)
  = do e' <- updateDecl newGlobal e
       es <- updateMDecl newGlobal rest
       pure (e' :: es)

-- [ Definition Declaration ]

update newGlobal End
  = pure End

update newGlobal (Local label x)
  = pure $ Local label x

update newGlobal (Global label {ty} x) with (isElem (label,ty) newGlobal)
  update newGlobal (Global label {ty} x) | (Yes idx)
    = Right (Global label (idx))

  update newGlobal (Global label {ty} x) | (No contra)
    = Left (IdentifierNotFound label)

update newGlobal (Let this beThis withType prf inThis)
  = do beThis' <- update newGlobal beThis
       wType'  <- update newGlobal withType
       inThis' <- update newGlobal inThis
       pure (Let this beThis' wType' prf inThis')

update newGlobal (Seq x y)
  = do x' <- update newGlobal x
       y' <- update newGlobal y
       pure (Seq x' y')

update newGlobal TYPE
  = pure TYPE

update newGlobal GATE
  = pure GATE

update newGlobal DataLogic
  = pure DataLogic

update newGlobal (DataEnum xs)
  = pure (DataEnum xs)

update newGlobal (DataArray type size)
  = do type' <- update newGlobal type
       pure (DataArray type' size)

update newGlobal (DataStruct xs)
  = do xs' <- updateKVs newGlobal xs
       pure (DataStruct xs')

update newGlobal (DataUnion xs)
  = do xs' <- updateKVs newGlobal xs
       pure (DataUnion xs')

update newGlobal (Port label dir type)
  = do type' <- update newGlobal type
       pure (Port label dir type')

update newGlobal (MDecl xs)
  = do xs' <- updateMDecl newGlobal xs
       pure (MDecl xs')

update newGlobal NewChan
  = pure NewChan

update newGlobal (NewModule xs)
  = do xs <- updatePorts newGlobal xs
       pure (NewModule xs)

update newGlobal (Not o i)
  = do x' <- update newGlobal o
       y' <- update newGlobal i
       pure (Not x' y')

update newGlobal (Gate ty o xs)
  = do o' <- update newGlobal o
       xs' <- traverse (update newGlobal) xs
       pure (Gate ty o' xs')

update newGlobal NoOp
  = pure NoOp

-- [ EOF ]
