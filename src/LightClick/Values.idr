module LightClick.Values

import Data.List
import Data.List.Elem

import Data.Vect
import Data.Vect.Elem

import Toolkit.Data.DList
import Toolkit.Data.DVect

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
mkDual : Value (PORT s) -> Either LightClick.Error (Value (PORT s))
mkDual (VLet _ _ _)  = Left $ NotSupposedToHappen (Just "mkDual")
mkDual (VSeq  _ _)   = Left $ NotSupposedToHappen (Just "mkDual")
mkDual (VRef _ _)    = Left $ NotSupposedToHappen (Just "mkDual")
mkDual (VIDX x y z)  = mkDual z
mkDual (VPort x IN    t) = Right (VPort x OUT t)
mkDual (VPort x OUT   t) = Right (VPort x IN t)
mkDual (VPort x INOUT t) = Right (VPort x INOUT t)

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

dualFan' : DVect String (Value . PORT) k names -> Either LightClick.Error (DVect String (Value . PORT) k names)
dualFan' Nil = Right Nil
dualFan' (x::xs) = do
   rest <- dualFan' xs
   d <- mkDual x
   pure (d :: rest)

export
dualFan : DVect String (Value . PORT) (S (S n)) names
       -> Either LightClick.Error
                 (DVect String (Value . PORT) (S (S n)) names)
dualFan (x::y::xs) = do
  x' <- mkDual x
  y' <- mkDual y
  xs' <- dualFan' xs
  pure (x'::y'::xs')

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
