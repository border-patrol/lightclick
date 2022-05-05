||| Transform our model with fancy connection primitives into a
||| simpler one with only modules, gates, and direct connections.
|||
||| Module    : Synthlify.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.Synthlify

import Data.List.Quantifiers
import Data.Vect
import Data.Vect.Elem

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.Location

import Toolkit.DeBruijn.Environment

import Language.SystemVerilog.Gates
import Language.SystemVerilog.Utilities

import LightClick.Core
import LightClick.Error

import LightClick.Types.Meta
import LightClick.Types
import LightClick.Connection

import LightClick.Terms
import LightClick.Values

%default total

||| We need this to ensure the types are translated correctly.
data Value : Item -> Type where
  V : Erase i (m ** ty) -> Value (interp m) -> Value i


||| Interpretation environment.
Env : List Item -> Type
Env = Env Item Value

||| Ensure the type-level context is used.
useFV : (env : Env old)
     -> (prf : UseFreeVar old idx new)
            -> Env new
useFV (V E elem :: rest) (UH prfU)
  = V E elem :: rest

useFV (elem :: rest) (UT x)
  = elem :: useFV rest x

||| Ensure the type-level context is used.
useFP : (env : Env old)
     -> (prf : UseFreePort old idx new)
            -> Env new
useFP (V E elem :: rest) (UH x prfU)
  = V E elem :: rest
useFP (elem :: rest) (UT x)
  = elem :: useFP rest x

||| Extract the port from the environment.
getPort : (env : Env old)
       -> (prf : FreePort label i old)
              -> LightClick (Value (PORT label))
getPort ((V E (VModule x)) :: rest) (Here (IFP (FE idx prf)))
      = pure (doGet x idx)
    where
      doGet : (ports : DVect String (Value . Values.PORT) n names)
           -> (idx   : Elem label names)
                    -> Value (PORT label)
      doGet (ex :: y) Here = ex
      doGet (ex :: y) (There later) = doGet y later

getPort (V E _ :: rest) (Here (IFP prf))
  = throw (NotSupposedToHappen (Just "Get Port"))

getPort (elem :: rest) (There later)
  = getPort rest later


-- [ Declarations ]

-- ## Terms

data Result : (ctxt : List Item)
           -> {m    : MTy}
           -> (type : Ty m)
                   -> Type
  where
    R : (env : Env ctxt)
     -> (v   : Value (interpTy type))
            -> Result ctxt type

term : {ctxt  : Context}
    -> (env   : Env ctxt)
    -> {m     : MTy}
    -> {type  : Ty m}
    -> (term  : Term ctxt type new)
             -> LightClick (Result new type)

data Fields : (ctxt  : List Item)
           -> (n     : Nat)
                    -> Type
  where
    F : {ctxt   : Context}
     -> (env    : Env ctxt)
     -> (fields : Vect n (Pair String (Value DATA)))
               -> Fields ctxt n

-- ## Fields
fields : {old : Context}
      -> (env : Env old)
      -> {n   : Nat}
      -> {types : Vect n (Pair String (Ty DATA))}
      -> (fs  : Fields old n types new)
             -> LightClick (Fields new n)

-- ## Ports

data Ports : (ctxt : List Item)
          -> (n    : Nat)
          -> (names : Vect n String)
                  -> Type
  where
    P : {ctxt : Context}
     -> (env  : Env ctxt)
     -> (ports : DVect String (Value . Values.PORT) n names)
              -> Ports ctxt n names

ports : {old   : Context}
     -> (env   : Env old)
     -> {n     : Nat}
     -> {names : Vect n String}
     -> {types : DVect String (Ty . PORT) n names }
     -> (ps    : Ports old n types new)
              -> LightClick (Ports new n names)


data Fan : (ctxt  : List Item)
        -> (n     : Nat)
        -> (names : Vect n String)
                 -> Type
  where
    FA : {ctxt  : Context}
      -> (env   : Env ctxt)
      -> (ports : DVect String (Value . Values.PORT) n names)
               -> Fan ctxt n names

fan : {old   : Context}
   -> (env   : Env old)
   -> {n     : Nat}
   -> {names : Vect n String}
   -> {types : DVect String (Ty . PORT) n names }
   -> (fs    : Fan old n types new)
            -> LightClick (Fan new n names)

-- [ Definitions ]

-- ## Fans

fan env Empty
  = pure (FA env Nil)

fan env (Extend port rest)
  = do R b p <- term env port
       FA c rest <- fan b rest
       pure (FA c (p::rest))



-- ## Ports
ports env Empty
  = pure (P env Nil)

ports env (Extend port later)
  = do R b p <- term env port
       P c rest <- ports b later
       pure (P c (p::rest))


-- ## Fields

fields env Empty
  = pure (F env Nil)

fields env (Extend s tm rest)
  = do R b tm <- term env tm
       F c rest <- fields b rest
       pure (F c ((s,tm)::rest))


-- [ Terms ]

-- [ Structure ]

term env (Ref fc l prf use)
  = pure (R (useFV env use)
            (VRef l _))

term env (Let fc label this prf (II u) scope)
  = do R b this  <- term env this
       R Nil scope <- term (V E this :: b)
                           scope
         | R _ _ => throw (Err fc "oops")
       pure (R Nil (VLet label this scope))

term env (Seq this prf that)

  = do R b this <- term env this
       R c that <- term b   that

       pure (R c (VSeq this that))

-- [ DataTypes ]

term env (DataLogic fc)
  = pure (R env VDataLogic)

term env (DataArray fc size dtype)
  = do R b dtype <- term env dtype
       pure (R b (VDataArray dtype size))

term env (DataEnum fc xs)
  = pure (R env (VDataEnum xs))

term env (DataStruct fc xs)
  = do F b xs <- fields env xs
       pure (R b (VDataStruct xs))

term env (DataUnion fc xs)
  = do F b xs <- fields env xs
       pure (R b (VDataUnion xs))

-- [ Module Structures ]
term env (Port fc l d _ _ n dtype)
  = do R b dtype <- term env dtype
       pure (R b (VPort l d n dtype))

term env (Module fc ps)
  = do P b ports <- ports env ps
       pure (R b (VModule ports))

term env (Index fc {names} {port} mref label prf use getP)
  = do p <- getPort env prf
       let b = useFP env use
       pure (R b (VIDX label (VRef mref (MODULE names)) p))

-- [ Connections ]
term env (NoOp fc kind tm)
  = do R b tm <- term env tm
       pure (R b (VNoOp kind tm))

term env (Connect fc left right prf)

    = do R b l <- term env left
         R c r <- term b   right

         ty <- getData l

         nX <- genNameConn l
         nY <- genNameConn r

         let n = newName [nX,nY]

         pure (R c (VLet n (VChan ty) (newConn n l r)))

term env (FanOut fc input fs prf)
    = do R b i <- term env input
         FA c f <- fan b fs

         ty <- getData i

         nI <- genNameConn i
         nF <- genNameFan f
         let n = newName ["fan_out_from", nI, "to", nF]

         pure (R c (VLet n (VChan ty) (FanOut.newConn n i f)))

term env (Mux fc fs ctrl output prf)
    = do FA b  i <- fan env fs
         R  ec c <- term b ctrl
         R  ed o <- term ec output

         nO <- genNameConn o
         nC <- genNameConn c
         nF <- genNameFan  i
         nFS <- getNameFan i

         dC <- getData c
         dO <- getData o

         let mName = newName ["mux", nO, nC, nF]

         dualFS <- dualFan' ("input_") i
         dualC  <- mkDual "control_" c
         dualO  <- mkDual "output_" o

         let mRef = (VRef mName (MODULE (nC::nO::nFS)))
         fi <- FanIn.newConn (newName [mName, "fanin"]) dO mRef i dualFS
         pure (R ed (VLet mName
                         (VModule (dualC::dualO::dualFS))
                         (VLet (newName [mName, "control"])
                               (VChan dC)
                               (VLet (newName [mName, "output"])
                                     (VChan dO)
                                     (VSeq (Direct.newConn (newName [mName, "control"]) c (newIDX mRef dualC))
                                           (VSeq (Direct.newConn (newName [mName,"output"]) o (newIDX mRef dualO))
                                                 fi
                                           ))))))


-- [ GATES ]

term env (NOT fc left right prf)

    = do (R b l) <- term env left
         (R c r) <- term b right

         ty <- getData l
         nX <- genNameConn l
         nY <- genNameConn r

         let c_in_name  = newName ["not_in",  nX, nY]
         let c_out_name = newName ["not_out", nX, nY]

         pure (R c
                 (VLet c_in_name
                    (VChan ty)
                    (VLet c_out_name
                          (VChan ty)
                          (VSeq (Gate.newConn c_in_name l)
                                (VSeq (Gate.newConn c_out_name r)
                                      (VNot (VRef c_out_name CHAN)
                                            (VRef c_in_name  CHAN)))))))

term env (GATE fc ty fs output prf)
    = do FA b fs <- fan env fs
         R  c o  <- term b output

         tyO <- getData o
         nO  <- genNameConn o

         nF  <- genNameFan fs

         let c_out_name = newName [show ty, nO, nF, "out"]
         let c_in_name  = newName [show ty, nO, nF, "in"]

         (ins', conns) <- Gate.FanIn.newConn c_in_name tyO fs

         pure (R c (VLet c_out_name
                         (VChan tyO)
                         (VSeq conns
                               (VSeq (Gate.newConn c_out_name o)
                                     (VGate ty (VRef c_out_name CHAN) ins')))))

term env (End fc prf)
  = pure (R Nil VEnd)

||| Transform our model with fancy connection primitives into a
||| simpler one with only modules, gates, and direct connections.
export
synthlify : (term  : Term Nil TyUnit Nil)
                  -> LightClick (Value UNIT)
synthlify tm
  = do R Nil v <- term Nil tm
       pure v

-- [ EOF ]
