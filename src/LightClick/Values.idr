||| A simpler SoC Orchestration language with only modules, gates, and
||| direct connections.
|||
||| Module    : Values.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.Values

import Data.List
import Data.List.Elem

import Data.Vect
import Data.Vect.Elem

import Data.String

import Toolkit.Data.DList
import Toolkit.Data.DVect

import Language.SystemVerilog.Gates
import Language.SystemVerilog.Utilities

import LightClick.Core
import LightClick.Types
import LightClick.Terms

%default total

||| Types.
public export
data TyValue : Type where
  PORT : (name : String) -> TyValue
  UNIT : TyValue
  MODULE : (names : (Vect (S n) String)) -> TyValue
  CONN : TyValue
  DATA : TyValue
  CHAN : TyValue
  GATE : TyValue

public export
data Value : TyValue -> Type where
  VRef  : (name : String)
       -> (type : TyValue)
               -> Value type

  VLet  : {term : TyValue}
       -> (name : String)
       -> (beThis : Value term)
       -> (inThis : Value expr)
                 -> Value expr

  VSeq  : {a,b : TyValue}
       -> (this     : Value a)
       -> (thenThis : Value b)
                   -> Value b

  VEnd : Value UNIT

  VPort : (label : String)
       -> (dir   : Direction)
       -> (n     : Necessity)
       -> (type  : Value DATA)
                -> Value (PORT label)

  VModule : {n : Nat}
         -> {names : Vect (S n) String}
         -> DVect String
                  (Value . PORT)
                  (S n)
                  names
         -> Value (MODULE names)

  VDataLogic : Value DATA

  VDataEnum : {n : Nat} -> Vect (S n) String -> Value DATA

  VDataArray : Value DATA
            -> Nat
            -> Value DATA

  VDataStruct : {n : Nat}
             -> Vect (S n) (Pair String (Value DATA))
             -> Value DATA

  VDataUnion  : {n : Nat}
             -> Vect (S n) (Pair String (Value DATA))
             -> Value DATA

  VChan : Value DATA -> Value CHAN

  VIDX : (name : String)
      -> (Value (MODULE names))
      -> (Value (PORT name))
      -> Value (PORT name)

  VConnD : Value CHAN
        -> Value (PORT i)
        -> Value (PORT o)
        -> Value CONN

  VConnFO : {m : Nat}
         -> {outs : Vect (S m) String}
         -> Value CHAN
         -> Value (PORT i)
         -> DVect String (Value . PORT) (S m) outs
         -> Value CONN

  VNot : Value CHAN
      -> Value CHAN
      -> Value GATE

  VGate : {n : Nat}
       -> TyGateComb
       -> Value CHAN
       -> Vect (S (S n)) (Value CHAN)
       -> Value GATE

  VConnG : Value CHAN
        -> Value (PORT p)
        -> Value CONN

  VNoOp : (kind : EndpointKind) -> Value (PORT p) -> Value CONN

-- [ Helper Functions ]

export
getType : {type : TyValue} -> Value type -> TyValue
getType {type} _ = type

||| Interpret from metatype.
public export
interp : MTy -> TyValue
interp (PORT x) = PORT x
interp UNIT = UNIT
interp (MODULE xs) = MODULE xs
interp CONN = CONN
interp DATA = DATA
interp GATE = GATE

public export
interpTy : {ty : MTy} -> Ty ty -> TyValue
interpTy {ty} _ = interp ty

-- [ Helper functions for constructing values ]

export
getData : Value (PORT s) -> LightClick (Value DATA)
getData (VRef x (PORT s))
  = throw (NotSupposedToHappen (Just "getData"))

getData (VLet x y z)
  = throw (NotSupposedToHappen (Just "getData"))

getData (VSeq x y)
  = throw (NotSupposedToHappen (Just "getData"))

getData (VPort x y w z)
  = pure z

getData (VIDX x y z)
  = getData z

export
genNameConn : Value (PORT s) -> LightClick String
genNameConn (VRef name (PORT s))
  = throw $ NotSupposedToHappen (Just "genNameConn ref")

genNameConn (VLet x y z)
  = throw $ NotSupposedToHappen (Just "genNameConn let")

genNameConn (VSeq x y)
  = throw $ NotSupposedToHappen (Just "genNameConn seq")

genNameConn (VPort x y w z)
  = pure x

genNameConn (VIDX x (VRef m (MODULE names)) z)
  = pure (newName [m,x])

genNameConn (VIDX x y z)
  = throw $ NotSupposedToHappen (Just $ "genNameConn idx non-ref" <+> show x)


export
mkDual : (n : String) -> Value (PORT s) -> LightClick (Value (PORT (n <+> s)))
mkDual n (VLet _ _ _)  = throw $ NotSupposedToHappen (Just "mkDual")
mkDual n (VSeq  _ _)   = throw $ NotSupposedToHappen (Just "mkDual")
mkDual n (VRef _ _)    = throw $ NotSupposedToHappen (Just "mkDual")
mkDual n (VIDX x y z)  = mkDual n z
mkDual n (VPort x IN    w t) = pure (VPort (n <+> x) OUT   w t)
mkDual n (VPort x OUT   w t) = pure (VPort (n <+> x) IN    w t)
mkDual n (VPort x INOUT w t) = pure (VPort (n <+> x) INOUT w t)

export
genNameFan : DVect String (Value . PORT) k names -> LightClick String
genNameFan Nil      = pure ""
genNameFan (x::Nil) = genNameConn x
genNameFan (x::xs) =
  do n <- genNameConn x
     rest <- genNameFan xs
     pure $ newName [n,rest]

export
getNameFan : DVect String (Value . PORT) k names
          -> LightClick (Vect k String)
getNameFan Nil      = pure Nil
getNameFan (x::Nil) = do n <- genNameConn x
                         pure [n]
getNameFan (x::xs) =
  do n <- genNameConn x
     rest <- getNameFan xs
     pure $ n :: rest

public export
fanPortNames : (p : String)
            -> (n : Nat)
            -> Vect n String
fanPortNames p Z = Nil
fanPortNames p (S k) = (p <+> "fan_" <+> show (S k) <+> "_") :: fanPortNames p k


dualFanG : {k : Nat}
        -> (ps : Vect k String)
        -> {names : Vect k String}
        -> DVect String (Value . PORT) k names
        -> LightClick (DVect String (Value . PORT) k (zipWith (<+>) ps names))
dualFanG Nil     Nil     = pure Nil
dualFanG (p::ps) (x::xs) = do
   rest <- dualFanG ps xs
   d <- mkDual p x
   pure (d :: rest)

export
dualFan : {n : Nat}
       -> (ps : Vect (S (S n)) String)
        -> {names : Vect (S (S n)) String}
       -> DVect String (Value . PORT) (S (S n)) names
       -> LightClick
                 (DVect String (Value . PORT) (S (S n)) (zipWith (<+>) ps names))
dualFan (p::q::ps) (x::y::xs)
  = do xs' <- dualFanG ps xs
       x' <- mkDual p x
       y' <- mkDual q y

       pure (x'::y'::xs')

export
dualFan' : {n     : Nat}
        -> (p     : String)
        -> {names : Vect (S (S n)) String}
        -> (ports : DVect String (Value . PORT) (S (S n)) names)
        -> LightClick
                 (DVect String (Value . PORT) (S (S n)) (zipWith (<+>) (fanPortNames p (S (S n))) names))
dualFan' p (x::y::xs) {n} = dualFan (fanPortNames p (S (S n))) (x::y::xs)

getPort' : DVect String (Value . PORT) n names
        -> Elem nam names
        -> LightClick (Value (PORT nam))
getPort' (y :: xs) Here          = pure y
getPort' (y::ys)   (There later) = getPort' ys later

export
getPort : DVect String (Value . PORT) (S n) names
       -> Elem nam names
       -> (LightClick $ Value (PORT nam))
getPort (z :: xs) Here = pure z
getPort (z :: xs) (There later) = getPort' xs later

export
getPortFromModule : Value (MODULE names)
                 -> Elem nam names
                 -> LightClick $ Value (PORT nam)
getPortFromModule (VLet x w s) z = throw $ NotSupposedToHappen (Just "getPrtFromModule")
getPortFromModule (VSeq x w)   z = throw $ NotSupposedToHappen (Just "getPrtFromModule")
getPortFromModule (VRef _ _)   z = throw $ NotSupposedToHappen (Just "getPrtFromModule")
getPortFromModule {nam} (VModule x)  z = getPort x z

namespace IndexBuilder
   export
   newIDX : {s : String}
         -> (m : Value (MODULE names))
         -> (port  : Value (PORT s))
         -> Value (PORT s)
   newIDX {s} = VIDX s

   export
   recoverRef : {names : Vect (S n) String}
             -> (m : Value (MODULE names))
             -> (label : String)
             -> Value (MODULE names)
   recoverRef {names} _ label = VRef label (MODULE names)

namespace ConnBuilder

  namespace Gate
    export
    newConn : (name : String)
           -> Value (PORT i)
           -> Value CONN
    newConn name i = (VConnG (VRef name CHAN) i)

    namespace FanIn
      helper : (cname : String)
            -> (n     : Nat)
            -> (dTy   : Value DATA)
            -> (iport : Value (PORT i))
                     -> LightClick (Value CHAN, Value CONN)
      helper cname n type src
        = let cname' = newName [cname, show n]
          in pure ( VRef cname' CHAN
                   , VLet cname'
                          (VChan type)
                          (Gate.newConn cname' src)
                   )

      newConn' : (c     : Nat)
              -> (cname : String)
              -> (type  : Value DATA)
              -> (is    : DVect String (Value . PORT) (S (S n)) ins)
                       -> LightClick
                                 ( Vect (S (S n)) (Value CHAN)
                                 , Value CONN)
      newConn' c name type (i::j::Nil)
        = do (i'', i') <- helper name c     type i
             (j'', j') <- helper name (S c) type j
             pure ([i'', j''], VSeq i' j')

      newConn' c name type (i::j::k::is)
        = do (rest', rest) <- newConn' (S (S c)) name type (j::k::is)
             (i'',   i')   <- helper name c type i
             pure (i''::rest', VSeq i' rest)

      export
      newConn : (cname : String)
             -> (type  : Value DATA)
             -> (is    : DVect String (Value . PORT) (S (S n)) ins)
                      -> LightClick
                                ( Vect (S (S n)) (Value CHAN)
                                , Value CONN
                                )
      newConn = newConn' Z

  namespace Direct
    export
    newConn : (name : String)
           -> Value (PORT ins)
           -> Value (PORT outs)
           -> Value CONN
    newConn name x y = (VConnD (VRef name CHAN) x y)

  namespace FanOut
    export
    newConn : {n : Nat}
           -> {outs : Vect (S n) String}
           -> (name : String)
           -> (is   : Value (PORT i))
           -> (os   : DVect String (Value . PORT) (S n) outs)
           -> Value CONN
    newConn name is os = (VConnFO (VRef name CHAN) is os)

  namespace FanIn
    export
    helper :  {o : String}
          -> (cname : String)
           -> (dTy   : Value DATA)
           -> (mod   : Value (MODULE names))
           -> (iport : Value (PORT i))
           -> (oport : Value (PORT o))
           -> LightClick (Value CONN)
    helper {o} cname dTy m x y = do
      nX <- genNameConn x
      nY <- genNameConn y
      let cname' = newName [cname, nX, nY]
      pure (VLet cname'
                   (VChan dTy)
                   (Direct.newConn cname' x (VIDX o m y)))

    export
    newConn : (cname : String)
           -> (Value DATA)
           -> (Value (MODULE names))
           -> (is : DVect String (Value . PORT) (S n) ins)
           -> (os : DVect String (Value . PORT) (S n) outs)
                 -> LightClick (Value CONN)
    newConn cname type m (i :: []) (o :: []) = helper cname type m i o
    newConn cname type m (i :: i' :: is) (o :: o' :: os)
      = do xy <- helper cname type m i o
           rest <- newConn cname type m (i'::is) (o'::os)
           pure (VSeq xy rest)

-- [ EOF ]
