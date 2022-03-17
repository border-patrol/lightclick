module LightClick.IR.ChannelCentric

import Data.List
import Data.String
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import Language.SystemVerilog.Gates

import LightClick.Core
import LightClick.Types.Necessity
import LightClick.Types.Direction
import LightClick.Error

import LightClick.IR.ModuleCentric

%default total

public export
data ChannelIR : TyIR -> Type where
  CRef  : String -> (type : TyIR) -> ChannelIR type
  CLet  : {term : TyIR}
       -> (bind : String)
       -> (this : ChannelIR term)
       -> (inThis : ChannelIR expr)
                 -> ChannelIR expr

  CSeq  : {a,b : TyIR}
       -> ChannelIR a
       -> ChannelIR b
       -> ChannelIR b

  CEnd : ChannelIR UNIT

  CPort : String
       -> Direction
       -> Necessity
       -> ChannelIR DATA
       -> ChannelIR PORT

  CModule : {n : Nat} -> Vect (S n) (ChannelIR PORT) -> ChannelIR MODULE

  CDataLogic : ChannelIR DATA
  CDataArray : ChannelIR DATA -> Nat -> ChannelIR DATA
  CDataStruct : {n : Nat} -> Vect (S n) (Pair String (ChannelIR DATA)) -> ChannelIR DATA
  CDataUnion  : {n : Nat} -> Vect (S n) (Pair String (ChannelIR DATA)) -> ChannelIR DATA

  CIDX : (label : String) -- don't exist in the normal form, required for mapping MIDX to something for coverage...
      -> ChannelIR MODULE
      -> ChannelIR PORT

  CChan : ChannelIR DATA -> ChannelIR CHAN

  CModuleInst : {n : Nat}
              -> (mname : ChannelIR MODULE)
              -> Vect (S n)
                      (Pair String (ChannelIR CHAN))
              -> ChannelIR CONN

  CNot : ChannelIR CHAN
      -> ChannelIR CHAN
      -> ChannelIR GATE

  CGate : {n : Nat}
       -> TyGateComb
       -> ChannelIR CHAN
       -> Vect (S (S n)) (ChannelIR CHAN)
       -> ChannelIR GATE

mutual

  namespace Vect
    export
    showC :  (kvs : Vect n (String, ChannelIR DATA))
                 -> Vect n String
    showC = map (\(l,c) => "(" <+> show l <+> " " <+> showC c <+> ")")

  namespace Data
    export
    showC : (kvs : Vect n (ChannelIR CHAN))
                -> Vect n String

    showC =  map (\c => "(" <+> showC c <+> ")")

  showC : ChannelIR type -> String
  showC (CRef name type) =
    "(CRef " <+> show name <+> " " <+> show type <+> ")"

  showC (CLet x y z) =
     "(CLet "
       <+> show x <+> " "
       <+> showC y <+> "\n"
       <+> showC z
       <+> "\n)"

  showC (CSeq x y) =
      "(CSeq "
        <+> showC x <+> " "
        <+> showC y
        <+> "\n)"
  showC CEnd = "(CEnd)"

  showC (CPort x y n z) =
      "(CPort "
        <+> show x <+> " "
        <+> show y <+> " "
        <+> show n <+> " "
        <+> showC z <+> " "
        <+> ")"

  showC (CModule x) =
      "(CModule "
        <+> show (map showC x)
        <+> ")"

  showC CDataLogic = "(CTyLogic)"

  showC (CDataArray x k) =
    "(CTyArray "
      <+> showC x <+> " "
      <+> show k
      <+> ")"

  showC (CDataStruct {n} xs) = "(CTyStruct " <+> show (showC xs) <+> ")"

  showC (CDataUnion {n} xs) = "(TyUnion " <+> show (showC xs) <+> ")"

  showC (CChan x) = "(CChan " <+> showC x <+> ")"

  showC (CIDX l m) =
    "(CIDX "
       <+> show l  <+> " "
       <+> showC m <+> " "
       <+> ")"

  showC (CModuleInst m {n} params) =
      "(CModuleInst "
        <+> showC m <+> " "
        <+> show ps
        <+> ")"
    where

      ps : Vect (S n) String
      ps = map (\(l,c) => show l <+> " " <+> showC c) params

  showC (CNot o i)
    = unwords ["(CNot", showC o, showC i, ")"]

  showC (CGate ty o ins)
      = unwords ["(CGate", show ty, showC o, show (showC ins), ")"]

export
Show (ChannelIR type) where
  show expr = showC expr

mutual
  namespace Port

    %inline
    convModule : ChannelIR MODULE -> LightClick (ChannelIR MODULE)
    convModule m@(CRef x MODULE)
      = pure m

    convModule (CLet x z w)
      = throw (NotSupposedToHappen (Just "convModule CIR let"))

    convModule (CSeq x z)
      = throw (NotSupposedToHappen (Just "convModule CIR CSeq"))

    convModule (CModule xs)
      = throw (NotSupposedToHappen (Just "convModule CIR CMod"))

    export
    convert : ModuleIR PORT -> LightClick (ChannelIR MODULE, String)
    convert (MRef name PORT)
      = throw (NotSupposedToHappen (Just "convPort CIR Ref"))

    convert (MLet name beThis inThis)
      = throw (NotSupposedToHappen (Just "convPort CIR Let"))
    convert (MSeq doThis thenThis)
      = throw (NotSupposedToHappen (Just "convPort CIR Seq"))
    convert (MPort label dir n type) =
       throw (NotSupposedToHappen (Just "convPort CIR Port"))

    convert (MIDX label x)
        = do m' <- convert x
             m'' <- convModule m'
             pure (m'',label)

  namespace Ports
    export
    %inline
    mkConn : (p : ModuleIR PORT)
          -> (c : ChannelIR CHAN)
               -> LightClick (ChannelIR CONN)
    mkConn p c
      = do (m,l) <- Port.convert p
           pure (CModuleInst m [(l,c)])

    export
    convert : (c  : ChannelIR CHAN)
           -> (os : Vect (S n) (ModuleIR  PORT))
                 -> LightClick (ChannelIR CONN)
    convert c (x :: []) = mkConn x c
    convert c (x :: (y :: xs))
      = do c' <- mkConn x c
           cs <- convert c (y::xs)
           pure (CSeq c' cs)


  convert : ModuleIR type
         -> LightClick (ChannelIR type)

  convert (MRef x t)
    = pure (CRef x t)

  convert (MLet x y z)
    = do y' <- convert y
         z' <- convert z
         pure $ CLet x y' z'

  convert (MSeq x y) =
    do x' <- convert x
       y' <- convert y
       pure $ CSeq x' y'
  convert MEnd = pure CEnd

  convert (MPort x y n z) =
    do z' <- convert z
       pure $ CPort x y n z'

  convert (MModule {n} x) =
      do xs <- traverse convert x
         pure $ CModule xs

  convert MDataLogic = pure CDataLogic

  convert (MDataArray x k) =
    do x' <- convert x
       pure $ CDataArray x' k
  convert (MDataStruct xs) =
      do xs' <- traverse (\(l,x) => do {x' <- convert x; pure (l, x')}) xs
         pure $ CDataStruct xs'

  convert (MDataUnion xs)  =
      do xs' <- traverse (\(l,x) => do {x' <- convert x; pure (l,x')}) xs
         pure $ CDataUnion xs'

  convert (MChan x) =
    do x' <- convert x
       pure (CChan x')

  convert (MIDX x s) =
    do s' <- convert s
       pure (CIDX x s')

  convert (MConn cname y ps) =
      do c <- convert cname
         i <- mkConn y c
         rest <- convert c ps
         pure (CSeq i rest)

  convert (MNot o i)
    = do o' <- convert o
         i' <- convert i
         pure (CNot o' i')

  convert (MGate ty o ins)
    = do o' <- convert o
         rest <- traverse convert ins
         pure (CGate ty o' rest)

  convert (MConnG c idx)
    = do c' <- convert c
         p  <- mkConn idx c'
         pure p

export
channelise : (m : ModuleIR type) -> LightClick (ChannelIR type)
channelise = convert

-- [ EOF ]
