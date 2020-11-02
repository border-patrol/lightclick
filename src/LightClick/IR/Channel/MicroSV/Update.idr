module LightClick.IR.Channel.MicroSV.Update

import Data.Vect
import Data.DList
import Data.DList.DeBruijn

import LightClick.IR.ModuleCentric

import LightClick.IR.Channel.MicroSV.Error

import Language.SystemVerilog.MetaTypes
import Language.SystemVerilog.Micro


%default covering -- this file has caused the totality checker to hang.

export
update : (newGlobal : Context)
      -> (expr : Expr local globalOld type)
      -> Either TError (Expr local newGlobal type)


updateKV : (newGlobal : Context)
        -> (String, Expr local globalOld type)
        -> Either TError (String, Expr local newGlobal type)
updateKV newGlobal (k,v) =
    do v' <- update newGlobal v
       pure (k,v')

updateKVs : (newGlobal : Context)
         -> (es : Vect n (String, Expr local global type))
         -> Either TError (Vect n (String, Expr local newGlobal type))
updateKVs newGlobal = traverse (updateKV newGlobal)

updateDecl : (newGlobal : Context)
          -> (expr : Expr local globalOld (PORT s))
         -> Either TError (Expr local newGlobal (PORT s))
updateDecl newGlobal = update newGlobal

updateMDecl : (newGlobal : Context)
         -> (ps : DList String (\s => Expr lctxt gctxt (PORT  s)) names)
         -> Either TError (DList String (\s => Expr lctxt newGlobal (PORT s)) names)
updateMDecl newGlobal [] = pure Nil
updateMDecl newGlobal (e :: rest) =
    do e' <- updateDecl newGlobal e
       es <- updateMDecl newGlobal rest
       pure (e' :: es)

update newGlobal End = pure End
update newGlobal (Local label x) = pure $ Local label x
update newGlobal (Global label {ty} x) with (isElem (label,ty) newGlobal)
  update newGlobal (Global label {ty} x) | (Yes idx) = Right (Global label (idx))

  update newGlobal (Global label {ty} x) | (No contra) = Left (IdentifierNotFound label)


update newGlobal (Let this beThis withType prf inThis) =
    do beThis' <- update newGlobal beThis
       wType'  <- update newGlobal withType
       inThis' <- update newGlobal inThis
       pure (Let this beThis' wType' prf inThis')
update newGlobal (Seq x y) =
    do x' <- update newGlobal x
       y' <- update newGlobal y
       pure (Seq x' y')
update newGlobal TYPE = pure TYPE
update newGlobal DataLogic = pure DataLogic
update newGlobal (DataArray type size) =
    do type' <- update newGlobal type
       pure (DataArray type' size)
update newGlobal (DataStruct xs) =
    do xs' <- updateKVs newGlobal xs
       pure (DataStruct xs')

update newGlobal (DataUnion xs) =
    do xs' <- updateKVs newGlobal xs
       pure (DataUnion xs')

update newGlobal (Port label dir type) =
    do type' <- update newGlobal type
       pure (Port label dir type')
update newGlobal (MDecl xs) =
    do xs' <- updateMDecl newGlobal xs
       pure (MDecl xs')
update newGlobal NewChan = pure NewChan
update newGlobal (NewModule xs) =
    do xs' <- traverse (updateKV newGlobal) xs
       pure (NewModule xs')


-- [ EOF ]
