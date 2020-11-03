module LightClick.Check

import Decidable.Equality

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DList.DeBruijn
import Toolkit.Data.DVect

import Toolkit.Data.Location
import Toolkit.Data.Rig

import Language.SystemVerilog.Utilities

import LightClick.Error

import LightClick.Types
import LightClick.Types.Equality
import LightClick.Terms

import LightClick.Connection

import LightClick.Values
import LightClick.Env

%default covering

public export
TyCheck : Type -> Type
TyCheck = Either LightClick.Error

mutual
  namespace Field

    hasKey : (fc    : FileContext)
          -> (label : String)
          -> (store : List String)
                   -> TyCheck (List String)
    hasKey fc label store with (isElem label store)
      hasKey fc label store | Yes prf =
        Left (LabelAlreadyExists fc label store)
      hasKey fc label store | No contra = Right (label :: store)

    export
    check : (env   : Env ctxt)
         -> (key   : String)
         -> (value : Term ctxt DATA)
         -> (store : List String)
         -> TyCheck ( Pair String (Value DATA)
                    , Pair String (Ty DATA)
                    , List String
                    , Env ctxt
                    )
    -- References are special
    check env key (Ref {label} fc idx) store
      = do (v,t,env') <- check env (Ref fc idx)
           store' <- hasKey fc key store
           pure ((key, VRef label DATA), (key,t), store, env' )

    -- Rest is normal
    check env key term store
      = do (v,t,env') <- check env term
           fc <- getFC term
           store' <- hasKey fc key store
           pure ((key,v), (key,t), store, env')


  namespace Fields
    export
    check : {n : Nat}
         -> (env   : Env ctxt)
         -> (kvs   : Vect (S n) (Pair String (Term ctxt DATA)))
         -> (store : List String)
                  -> TyCheck
                         ( Vect (S n) (Pair String (Value DATA))
                         , Vect (S n) (Pair String (Ty DATA))
                         )
    check {n = n} env ((k,v) :: xs) store with (check env k v store)
      check {n = n} env ((k,v) :: xs) store | Left err = Left err
      check {n = n} env ((k,v) :: xs) store | Right (kv, kt, store', env') with (xs)
        check {n = Z} env ((k,v) :: Nil) store | Right (kv, kt, store', env') | Nil
          = pure ([kv], [kt])
        check {n = S n} env ((k,v) :: xs) store | Right (kv, kt, store', env') | (y::ys)
          = do (kvs, kts) <- check env' (y::ys) store'
               pure ((kv::kvs), kt::kts)

  namespace Modules

    export
    check : (env   : Env ctxt)
         -> (ports : DVect String
                           (\s => Term ctxt (PORT s))
                           (S n)
                           names)
         -> TyCheck ( DVect String (Value . PORT) (S n) names
                    , DVect String (Ty . PORT)    (S n) names
                    , Env ctxt)
    check {n = n} env (ex :: rest) with (Check.check env ex)
      check {n = n} env (ex :: rest) | (Left l) = Left l
      check {n = n} env (ex :: rest) | (Right (valueX, typeX, env')) with (rest)
        check {n = Z} env (ex :: Nil) | (Right (valueX, typeX, env')) | Nil
          = Right ([valueX], [typeX], env')
        check {n = S n} env (ex :: xs) | (Right (valueX, typeX, env')) | (y::ys)
          = do (pvs, pts, env'') <- Modules.check env' (y::ys)
               Right (valueX::pvs, typeX::pts, env'')

  namespace Port
    export
    use : {s : String} -> FileContext -> Ty (PORT s) -> TyCheck (Ty (PORT s))
    use fc type {s} = do u <- shiftUsage fc s (getUsage type)
                         Right (setUsage type u)

      where
        shiftUsage : FileContext -> String -> TyRig -> TyCheck TyRig
        shiftUsage fc s None  = Left (PortInUse fc s)
        shiftUsage _  _ One   = Right None
        shiftUsage _  _ Tonne = Right Tonne

    export
    check : (env  : Env ctxt)
         -> (term : Term ctxt (PORT s))
                 -> TyCheck (Value (PORT s), Ty (PORT s), Env ctxt)

    check env (Ref fc idx) with (Check.check env (Ref fc idx))
      check env (Ref fc idx) | Left l = Left l
      check env (Ref fc idx) | Right (v,t,env') with (t)
        check env (Ref fc idx) | Right (v,t,env') | portTy with (use fc portTy)
          check env (Ref fc idx) | Right (v,t,env') | portTy | Left l = Left l
          check env (Ref fc idx) | Right (v,t,env') | portTy | Right portTy'
            = do let env'' = updateWith env' idx (\(MkEntry value (MkTheType s portTy)) => MkEntry value (MkTheType s portTy'))
                 Right (v,portTy', env'')

    -- projection is just projection
    check env (Index fc mod idx) = Check.check env (Index fc mod idx)

    -- Seqs and Lets are not supposed to be here.
    check env _ = Left (NotSupposedToHappen (Just "Port.check"))

  namespace Fan

    export
    check : (env   : Env ctxt)
         -> (ports : DVect String
                           (\s => Term ctxt (PORT s))
                           (S (S n))
                           names)
         -> TyCheck
                   ( DVect String (Value . PORT) (S (S n)) names
                   , DVect String (Ty . PORT)    (S (S n)) names
                   , Env ctxt)
    check {n = n} env (x::y::xs) with (Port.check env x)
      check {n = n} env (x::y::xs) | Left l = Left l

      check {n = n} env (x::y::xs) | Right (vx,tx,ex) with (xs)
        check {n = Z} env (x::y::xs) | Right (vx,tx,ex) | Nil with (Port.check ex y)
          check {n = Z} env (x::y::xs) | Right (vx,tx,ex) | Nil | Left l
            = Left l
          check {n = Z} env (x::y::xs) | Right (vx,tx,ex) | Nil | Right (vy,ty,ey)
            = Right ([vx,vy], [tx,ty], ey)

        check {n = S n} env (x::y::xs) | Right (vx,tx,ex) | (z::zs) with (Fan.check ex (y::z::zs))
          check {n = S n} env (x::y::xs) | Right (vx,tx,ex) | (z::zs) | Left l = Left l
          check {n = S n} env (x::y::xs) | Right (vx,tx,ex) | (z::zs) | Right (vs, ts, env')
            = Right ((vx::vs), (tx::ts), env')


  -- [ Top Level Check Definition Begins Here ]

  export
  check : (env  : Env ctxt)
       -> (term : Term ctxt mty)
       -> TyCheck (Value (interp mty), Ty mty, Env ctxt)



  -- [ Checking References ]
  check env (Ref fc prf) with (read prf env)
    check env (Ref fc prf) | (MkEntry value (MkTheType name type))
      = Right (value, type, env)

  -- [ Checking Let Bindings ]
  check env (Let fc label this inThis)
    = do (ev, et, env') <- check env this
         (bv, bt, (u::env'')) <- check (MkEntry ev (MkTheType label et)::env') inThis
         Right (VLet label ev bv, bt, env'')

  -- [ Checking Sequencing ]
  check env (Seq x y)
    = do (vX, tX, env') <- check env x
         (vY, tY, env'') <- check env' y
         Right (VSeq vX vY, tY, env'')

  -- [ Checking Data Types]

  -- Logic
  check env (DataLogic fc) = Right (VDataLogic, TyLogic, env)

  -- Arrays
  check env (DataArray fc type size)
    = do (vs, ty', env') <- check env type
         Right (VDataArray vs size, TyArray ty' size, env')

  -- Data Strucutres

  -- Structs

  check env (DataStruct fc kvs)
    = do (kvalues, ktypes) <- check env kvs Nil
         Right (VDataStruct kvalues, TyStruct ktypes, env)

  -- Unions
  check env (DataUnion fc kvs)
    = do (kvalues, ktypes) <- check env kvs Nil
         Right (VDataUnion kvalues, TyUnion ktypes, env)


  -- [ Checking Ports ]
  check env (Port fc l d s w (Ref {label} x y))
    = do (v, t, env') <- check env (Ref x y)
         Right (VPort l d (VRef label DATA), TyPort l d s w t One, env')

  check env (Port fc l d s w term)
    = do (v, t, env') <- check env term
         Right (VPort l d v, TyPort l d s w t One, env')

  -- [ Checking Modules ]

  check env (Module fc ports)
    = do (vs, ts, env') <- check env ports
         Right (VModule vs, TyModule ts, env')

  -- [ Checking Module projection ]

  check env (Index fc m idx) with (check env m)
    check env (Index fc m idx) | Left l = Left l
    check env (Index fc (Ref fc' {label} midx) idx) | Right (v, t, env') with (t)
      check env (Index fc (Ref fc' {label} midx) idx) | Right (v, t, env') | TyModule names with (index names idx)
        check env (Index fc (Ref fc' {label} midx) idx) | Right (v, t, env') | TyModule names | portTy with (use fc portTy)
          check env (Index fc (Ref fc' {label} midx) idx) | Right (v, t, env') | TyModule names | portTy | Left l = Left l
          check env (Index fc (Ref fc' {label} midx) idx) | Right (v, t, env') | TyModule names | portTy | Right portTy'
            = do let names' = update names idx portTy'
                 let env''  = updateWith env' midx (\(MkEntry value (MkTheType s (TyModule names))) => MkEntry value (MkTheType s (TyModule names')))
                 port <- getPortFromModule v idx
                 Right (newIDX (recoverRef v label) port, portTy, env'')

    check env (Index fc _ idx) | Right (v, t, env') = Left (ConstantsNotAllowed fc)

  -- [ Checking Direct Connections ]

  check env (Connect fc left right)
    = do (vX, tyX, envx) <- Port.check env  left
         (vY, tyY, envy) <- Port.check envx right

         case compatible tyX tyY of
           No msg contra => Left (UnSafeDirectConnection fc msg)
           Yes prf => do
             ty <- getData vX

             nX <- genNameConn vX
             nY <- genNameConn vY
             let n = newName [nX,nY]

             Right (VLet n (VChan ty) (newConn n vX vY), TyConn, envy)

  -- [ Checking Fanouts]

  check env (FanOut fc i fan)
    = do (vI, tyIN,  envi) <- Port.check env i
         (vF, tyFAN,  envf) <- Fan.check envi fan
         case Fanout.compatible tyIN tyFAN of
           No (PListError pos reason) contra => do
             Left (UnSafeFan fc FANOUT pos reason)

           Yes prf => do
               ty <- getData vI

               nI <- genNameConn vI
               nF <- genNameFan vF
               let n = newName ["fan_out_from", nI, "to", nF]
               Right (VLet n (VChan ty) (newConn n vI vF) , TyConn, envf)

  -- [ Checking Multiplexers ]

  check env (Mux fc fan ctrl o)
    = do (fs, tf, envf) <- Fan.check  env  fan
         (vC, tc, envc) <- Port.check envf ctrl
         (vO, to, envo) <- Port.check envc o

         case Mux.compatible tf tc to of
           No (CtrlNotSafe x) contra =>
                Left (UnSafeMuxCtrl !(getFC ctrl) x)
           No (MuxNotSafe (PListError pos reason)) contra => do

             Left (UnSafeFan fc FANIN pos reason)
           Yes prf => do
             nO <- genNameConn vO
             nC <- genNameConn vC
             nF <- genNameFan  fs
             nFS <- getNameFan fs

             dC <- getData vC
             dO <- getData vO

             let mName = newName ["mux", nO, nC, nF]

             dualFS <- dualFan fs
             dualC  <- mkDual vC
             dualO  <- mkDual vO

             let mRef = (VRef mName (MODULE (nC::nO::nFS)))
             fi <- newConn (newName [mName, "fanin"]) dO mRef fs dualFS
             Right (VLet mName
                           (VModule (dualC::dualO::dualFS))
                           (VLet (newName [mName, "control"])
                                 (VChan dC)
                                 (VLet (newName [mName, "output"])
                                       (VChan dO)
                                       (VSeq (Direct.newConn (newName [mName, "control"]) vC (newIDX mRef vC))
                                             (VSeq (Direct.newConn (newName [mName,"output"]) vO (newIDX mRef vO))
                                                   fi
                                             )
                                       )

                                   )
                           )
                   , TyConn, envo)

  check env End with (free env)
    check env End | Nil = Right (VEnd, TyUnit, env)
    check env End | (x::xs) = Left (UnusedPorts (x::xs))

export
runCheck : (term : Term Nil UNIT) -> TyCheck (Value UNIT)
runCheck term with (check Nil term)
  runCheck term | (Left l) = Left l
  runCheck term | (Right (value, ty, env)) = Right (value)


-- [ EOF ]
