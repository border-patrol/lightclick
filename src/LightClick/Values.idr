module LightClick.Values

import Data.List
import Data.List.Elem

import Data.Vect
import Data.Vect.Elem

import Toolkit.Data.DList
import Toolkit.Data.DVect

import Language.SystemVerilog.Gates
import Language.SystemVerilog.Utilities

import LightClick.Types
import LightClick.Terms
import LightClick.Error

%default total

public export
data TyValue : Type where
  PORT : (name : String) -> TyValue
  UNIT : TyValue
  MODULE : (names : (Vect (S n) String)) -> TyValue
  CONN : TyValue
  DATA : TyValue
  CHAN : TyValue

public export
data Value : TyValue -> Type where
  VRef  : (name : String) -> (type : TyValue) -> Value type

  VLet  : {term : TyValue} -> (name : String)
       -> (beThis : Value term)
       -> (inThis : Value expr) -> Value expr

  VSeq  : {a,b : TyValue} -> (this     : Value a)
       -> (thenThis : Value b) -> Value b

  VEnd : Value UNIT

  VPort : (label : String)
       -> (dir   : Direction)
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
  VDataArray : Value DATA -> Nat -> Value DATA
  VDataStruct : {n : Nat} -> Vect (S n) (Pair String (Value DATA)) -> Value DATA
  VDataUnion  : {n : Nat} -> Vect (S n) (Pair String (Value DATA)) -> Value DATA

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

export
getType : {type : TyValue} -> Value type -> TyValue
getType {type} _ = type


covering
showV : Value type -> String
showV (VRef name type) =
  "(VRef " <+> show name
    <+> ")"

showV (VLet x y z) =
   "(VLet "
     <+> show x <+> " "
     <+> showV y <+> " "
     <+> showV z
     <+> ")"

showV (VSeq x y) =
    "(VSeq "
      <+> showV x <+> " "
      <+> showV y
      <+> ")"
showV VEnd = "(VEnd)"

showV (VPort x y z) =
    "(VPort "
      <+> show x <+> " "
      <+> show y <+> " "
      <+> showV z <+> " "
      <+> ")"

showV (VModule x) =
    "(VModule "
      <+> showDVect showV x
      <+> ")"

showV VDataLogic = "(VTyLogic)"

showV (VDataArray x k) =
  "(VTyArray "
    <+> showV x <+> " "
    <+> show k
    <+> ")"

showV (VDataStruct {n} xs) = "(VTyStruct " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showV c <+> ")") xs

showV (VDataUnion {n} xs) = "(TyUnion " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showV c <+> ")") xs


showV (VChan x) = "(VChan " <+> showV x <+> ")"

showV (VIDX x y z) =
    "(VIndex "
       <+> show x <+> " "
       <+> showV y <+> " "
       <+> showV z
       <+> ")"

showV (VConnD x y z) =
    "(VDConn "
      <+> showV x <+> " "
      <+> showV y <+> " "
      <+> showV z <+> " "
      <+> ")"

showV (VConnFO x y z) =
    "(VFConn "
      <+> showV x <+> " "
      <+> showV y <+> " "
      <+> showDVect showV z <+> " "
      <+> ")"

export
Show (Value type) where
  show = assert_total showV -- TODO


public export
interp : MTy -> TyValue
interp (PORT x) = PORT x
interp UNIT = UNIT
interp (MODULE xs) = MODULE xs
interp CONN = CONN
interp DATA = DATA

export
getData : Value (PORT s) -> Either LightClick.Error (Value DATA)
getData (VRef x (PORT s)) = Left (NotSupposedToHappen (Just "getData"))
getData (VLet x y z)      = Left (NotSupposedToHappen (Just "getData"))
getData (VSeq x y)        = Left (NotSupposedToHappen (Just "getData"))
getData (VPort x y z) = Right z
getData (VIDX x y z) = getData z

export
genNameConn : Value (PORT s) -> Either LightClick.Error String
genNameConn (VRef name (PORT s)) = Left $ NotSupposedToHappen (Just "genNameConn ref")
genNameConn (VLet x y z)         = Left $ NotSupposedToHappen (Just "genNameConn let")
genNameConn (VSeq x y)           = Left $ NotSupposedToHappen (Just "genNameConn seq")
genNameConn (VPort x y z) = Right x
genNameConn (VIDX x (VRef m (MODULE names)) z) = Right (newName [m,x])
genNameConn (VIDX x y z) = Left $ NotSupposedToHappen (Just $ "genNameConn idx non-ref" <+> show y)


export
mkDual : (n : String) -> Value (PORT s) -> Either LightClick.Error (Value (PORT (n <+> s)))
mkDual n (VLet _ _ _)  = Left $ NotSupposedToHappen (Just "mkDual")
mkDual n (VSeq  _ _)   = Left $ NotSupposedToHappen (Just "mkDual")
mkDual n (VRef _ _)    = Left $ NotSupposedToHappen (Just "mkDual")
mkDual n (VIDX x y z)  = mkDual n z
mkDual n (VPort x IN    t) = Right (VPort (n <+> x) OUT t)
mkDual n (VPort x OUT   t) = Right (VPort (n <+> x) IN t)
mkDual n (VPort x INOUT t) = Right (VPort (n <+> x) INOUT t)

export
genNameFan : DVect String (Value . PORT) k names -> Either LightClick.Error String
genNameFan Nil      = Right ""
genNameFan (x::Nil) = genNameConn x
genNameFan (x::xs) =
  do n <- genNameConn x
     rest <- genNameFan xs
     pure $ newName [n,rest]

export
getNameFan : DVect String (Value . PORT) k names
          -> Either LightClick.Error (Vect k String)
getNameFan Nil      = Right Nil
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
        -> Either LightClick.Error (DVect String (Value . PORT) k (zipWith (<+>) ps names))
dualFanG Nil     Nil     = Right Nil
dualFanG (p::ps) (x::xs) = do
   rest <- dualFanG ps xs
   d <- mkDual p x
   pure (d :: rest)

export
dualFan : {n : Nat}
       -> (ps : Vect (S (S n)) String)
        -> {names : Vect (S (S n)) String}
       -> DVect String (Value . PORT) (S (S n)) names
       -> Either LightClick.Error
                 (DVect String (Value . PORT) (S (S n)) (zipWith (<+>) ps names))
dualFan (p::q::ps) (x::y::xs) = do
  xs' <- dualFanG ps xs
  x' <- mkDual p x
  y' <- mkDual q y

  pure (x'::y'::xs')

export
dualFan' : {n     : Nat}
        -> (p     : String)
        -> {names : Vect (S (S n)) String}
        -> (ports : DVect String (Value . PORT) (S (S n)) names)
        -> Either LightClick.Error
                 (DVect String (Value . PORT) (S (S n)) (zipWith (<+>) (fanPortNames p (S (S n))) names))
dualFan' p (x::y::xs) {n} = dualFan (fanPortNames p (S (S n))) (x::y::xs)

getPort' : DVect String (Value . PORT) n names
        -> Elem nam names
        -> Either LightClick.Error (Value (PORT nam))
getPort' (y :: xs) Here          = Right y
getPort' (y::ys)   (There later) = getPort' ys later

export
getPort : DVect String (Value . PORT) (S n) names
       -> Elem nam names
       -> (Either LightClick.Error $ Value (PORT nam))
getPort (z :: xs) Here = Right z
getPort (z :: xs) (There later) = getPort' xs later

export
getPortFromModule : Value (MODULE names)
                 -> Elem nam names
                 -> Either LightClick.Error $ Value (PORT nam)
getPortFromModule (VLet x w s) z = Left $ NotSupposedToHappen (Just "getPrtFromModule")
getPortFromModule (VSeq x w)   z = Left $ NotSupposedToHappen (Just "getPrtFromModule")
getPortFromModule (VRef _ _)   z = Left $ NotSupposedToHappen (Just "getPrtFromModule")
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
           -> Either LightClick.Error (Value CONN)
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
                 -> Either LightClick.Error (Value CONN)
    newConn cname type m (i :: []) (o :: []) = helper cname type m i o
    newConn cname type m (i :: i' :: is) (o :: o' :: os)
      = do xy <- helper cname type m i o
           rest <- newConn cname type m (i'::is) (o'::os)
           pure (VSeq xy rest)

-- --------------------------------------------------------------------- [ EOF ]
