module LightClick.DSL.Convert

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn

import Toolkit.Data.Location

import LightClick.Types
import LightClick.Terms
import LightClick.Error

import LightClick.DSL.AST

%default covering

public export
MetaTyCheck : Type -> Type
MetaTyCheck = Either LightClick.Error

convert : (ctxt : Context)
       -> (expr : AST)
       -> MetaTyCheck (type ** Term ctxt type)


expectPort : (ctxt : Context)
          -> (term : AST)
          -> MetaTyCheck (n ** Term ctxt (PORT n))
expectPort ctxt expr with (convert ctxt expr)
  expectPort ctxt expr | (Left l) = Left l
  expectPort ctxt expr | (Right (PORT n ** term)) = Right (n ** term)
  expectPort ctxt expr | (Right (type ** term)) = do
    loc <- getFC term
    Left (MetaTypeMismatch loc (PORT "") type)

checkType : (ctxt : Context)
         -> (type : MTy)
         -> AST
         -> MetaTyCheck (Term ctxt type)
checkType ctxt typeE ast with (convert ctxt ast)
  checkType ctxt typeE ast | (Left l) = Left l
  checkType ctxt typeE ast | (Right (typeG ** term)) with (decEq typeG typeE)
    checkType ctxt typeE ast | (Right (typeE ** term)) | (Yes Refl) = Right term
    checkType ctxt typeE ast | (Right (typeG ** term)) | (No contra) = do
        l <- getFC term
        Left (MetaTypeMismatch l typeE typeG)

doKVConvert : (ctxt : Context)
           -> (type : MTy)
           -> Pair String AST
           -> MetaTyCheck (Pair String (Term ctxt type))
doKVConvert ctxt type (k,v) = do
    v' <- checkType ctxt type v
    Right (k,v')

convertListPort : (ctxt : Context)
               -> (ps : Vect n AST)
               -> MetaTyCheck (ss : Vect n String
                                 **
                                DVect String
                                      (\s => Term ctxt (PORT s))
                                      n
                                      ss)

convertListPort ctxt [] = Right (_ ** Nil)
convertListPort ctxt (x :: xs) with (convert ctxt x)
  convertListPort ctxt (x :: xs) | (Left l) = Left l
  convertListPort ctxt (x :: xs) | (Right (PORT s ** term)) with (convertListPort ctxt xs)
    convertListPort ctxt (x :: xs) | (Right (PORT s ** term)) | (Left l) = Left l
    convertListPort ctxt (x :: xs) | (Right (PORT s ** term)) | (Right (ss ** ports)) = Right (s::ss ** term::ports)

  convertListPort ctxt (x :: xs) | (Right (type ** term)) = do
      loc <- getFC term
      Left (MetaTypeConstructionError loc (PORT "") type)


convertListPortM : (ctxt : Context)
                -> (ps : Vect (S n) AST)
                -> MetaTyCheck (ss : Vect (S n) String
                                 **
                                 DVect String
                                       (\s => Term ctxt (PORT s)) (S n)
                                       ss)
convertListPortM = convertListPort

convertListPortF : (ctxt : Context)
                -> (ps : Vect (S (S n)) AST)
                -> MetaTyCheck (ss : Vect (S (S n)) String
                                 **
                                 DVect String
                                       (\s => Term ctxt (PORT s)) (S (S n))
                                       ss)
convertListPortF = convertListPort

genIndex : (fc : FileContext)
        -> (ctxt : Context)
        -> (label : String)
        -> MetaTyCheck (type ** Index ctxt (label,type))
genIndex fc [] label =
  Left (IdentifierNotFound fc label)
genIndex fc ((x,t) :: xs) label with (decEq label x)
  genIndex fc ((x,t) :: xs) x | (Yes Refl) = Right (t ** Here)
  genIndex fc ((x,t) :: xs) label | (No contra) with (genIndex fc xs label)
    genIndex fc ((x,t) :: xs) label | (No contra) | (Left l) = Left l
    genIndex fc ((x,t) :: xs) label | (No contra) | (Right (type ** prf)) = Right (type ** There prf)

convert ctxt (Ref fc x) with (genIndex fc ctxt x)
  convert ctxt (Ref fc x) | (Left l) = Left l
  convert ctxt (Ref fc x) | (Right (type ** idx)) =
      Right (type ** Ref fc idx)


convert ctxt (Bind fc name expr body) with (genIndex fc ctxt name)
  convert ctxt (Bind fc name expr body) | (Left l) = do
    expr' <- convert ctxt expr
    body' <- convert ((name, fst expr')::ctxt) body
    Right (fst body' ** Let fc name (snd expr') (snd body'))
  convert ctxt (Bind fc name expr body) | (Right r) =
    Left (IdentifierAlreadyExists fc name)


convert ctxt (Seq exprA exprB) = do
   exprA' <- convert ctxt exprA
   exprB' <- convert ctxt exprB
   Right (fst exprB' ** Seq (snd exprA') (snd exprB'))


convert ctxt (DataLogic fc)      = Right (DATA ** DataLogic fc)

convert ctxt (DataArray fc ty l) = do
  term <- checkType ctxt DATA ty
  Right (DATA ** DataArray fc term l)

convert ctxt (DataStruct fc kvs) = do
    kvs' <- traverse (doKVConvert ctxt DATA) kvs
    Right (DATA ** DataStruct fc kvs')

convert ctxt (DataUnion fc kvs) = do
    kvs' <- traverse (doKVConvert ctxt DATA) kvs
    Right (DATA ** DataUnion fc kvs')

convert ctxt (Port fc l d s w t) = do
  dataType <- checkType ctxt DATA t
  Right (PORT l ** Port fc l d s w dataType)


convert ctxt (ModuleDef fc ps) = do
  ps' <- convertListPortM ctxt ps
  Right (MODULE (fst ps') ** Module fc $ snd ps')

convert ctxt (Index fc x b) with (convert ctxt x)
  convert ctxt (Index fc x b) | (Left l) = Left l
  convert ctxt (Index fc x b) | (Right (MODULE ns ** term)) with (isElem b ns)
    convert ctxt (Index fc x b) | (Right (MODULE ns ** term)) | (Yes prf) = Right (_ ** Index fc term prf)
    convert ctxt (Index fc x b) | (Right (MODULE ns ** term)) | (No contra) = do
      Left (InvalidModuleIndex fc b ns)

  convert ctxt (Index fc x b) | (Right (type ** term)) =
     Left (MetaTypeConstructionError fc (MODULE [""]) type)

convert ctxt (Connect fc x y) = do
  x' <- expectPort ctxt x
  y' <- expectPort ctxt y
  Right (CONN ** Connect fc (snd x') (snd y'))


convert ctxt (FanOut fc w ws) = do
   w'  <- expectPort ctxt w
   ws' <- convertListPortF ctxt ws
   Right (CONN ** FanOut fc (snd w') (snd ws'))

convert ctxt (Mux fc fan ctrl out) = do
  fan' <- convertListPortF ctxt fan
  ctrl' <- expectPort ctxt ctrl
  out'  <- expectPort ctxt out
  Right (CONN ** Mux fc (snd fan') (snd ctrl') (snd out'))

convert ctxt (NOT fc i o)
  = do x' <- expectPort ctxt i
       y' <- expectPort ctxt o
       Right (GATE ** NOT fc (snd x') (snd y'))

convert ctxt (GATE fc ty is o)
  = do is' <- convertListPortF ctxt is
       o'  <- expectPort ctxt o
       Right (GATE ** GATE fc ty (snd is') (snd o'))

convert ctxt End = Right (UNIT ** End)

export
runConvert : AST -> MetaTyCheck (Term Nil UNIT)
runConvert ast with (convert Nil ast)
  runConvert ast | (Left l) = Left l
  runConvert ast | (Right (UNIT ** term)) = Right term
  runConvert ast | (Right (type ** term)) = Left (NotSupposedToHappen $ Just "runConvert")
