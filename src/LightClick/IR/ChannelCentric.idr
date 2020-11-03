module LightClick.IR.ChannelCentric

import Data.List
import Data.Vect

import Toolkit.Data.DList
import Toolkit.Data.DVect

import LightClick.Types
import LightClick.Terms
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
       -> ChannelIR DATA
       -> ChannelIR PORT

  CModule : Vect (S n) (ChannelIR PORT) -> ChannelIR MODULE

  CDataLogic : ChannelIR DATA
  CDataArray : ChannelIR DATA -> Nat -> ChannelIR DATA
  CDataStruct : {n : Nat} -> Vect (S n) (Pair String (ChannelIR DATA)) -> ChannelIR DATA
  CDataUnion  : {n : Nat} -> Vect (S n) (Pair String (ChannelIR DATA)) -> ChannelIR DATA

  CIDX : (label : String) -- don't exist in the normal form, required for mapping MIDX to something for coverage...
      -> ChannelIR MODULE
      -> ChannelIR PORT
      -> ChannelIR PORT

  CChan : ChannelIR DATA -> ChannelIR CHAN

  CModuleInst : (mname : ChannelIR MODULE)
              -> Vect (S n)
                      (Pair String (ChannelIR CHAN))
              -> ChannelIR CONN


covering
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

showC (CPort x y z) =
    "(CPort "
      <+> show x <+> " "
      <+> show y <+> " "
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

showC (CDataStruct {n} xs) = "(CTyStruct " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showC c <+> ")") xs

showC (CDataUnion {n} xs) = "(TyUnion " <+> show ps <+> ")"
  where
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => "(" <+> show l <+> " " <+> showC c <+> ")") xs

showC (CChan x) = "(CChan " <+> showC x <+> ")"

showC (CIDX l m p) =
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
    covering
    ps : Vect (S n) String
    ps = map (\(l,c) => show l <+> " " <+> showC c) params

export
Show (ChannelIR type) where
  show expr = assert_total $ showC expr

public export
Convert : Type -> Type
Convert = Either LightClick.Error

covering
convert : ModuleIR type -> Convert (ChannelIR type)
convert (MRef x t) = Right $ CRef x t
convert (MLet x y z) =
  do y' <- convert y
     z' <- convert z
     pure $ CLet x y' z'
convert (MSeq x y) =
  do x' <- convert x
     y' <- convert y
     pure $ CSeq x' y'
convert MEnd = pure CEnd

convert (MPort x y z) =
  do z' <- convert z
     pure $ CPort x y z'

convert (MModule {n} x) =
    do xs <- convertPS x
       pure $ CModule xs
  where
    convertPS : Vect y (ModuleIR PORT) -> Convert (Vect y (ChannelIR PORT))
    convertPS [] = Right Nil
    convertPS (y :: xs) =
       do y' <- convert y
          rest <- convertPS xs
          pure (y'::rest)

convert MDataLogic = Right $ CDataLogic

convert (MDataArray x k) =
  do x' <- convert x
     pure $ CDataArray x' k
convert (MDataStruct xs) =
    do xs' <- convertKVs xs
       pure $ CDataStruct xs' -- (map (\(k,v) => MkPair k (convert v)) xs)
  where
    convertKVs : Vect y (String, ModuleIR DATA) -> Convert (Vect y (String, ChannelIR DATA))
    convertKVs [] = Right Nil
    convertKVs ((l,x) :: xs) =
     do x' <- convert x
        rest <- convertKVs xs
        pure ((l,x')::rest)


convert (MDataUnion xs)  =
    do xs' <- convertKVs xs
       pure $ CDataUnion xs' -- (map (\(k,v) => MkPair k (convert v)) xs)
  where
    convertKVs : Vect y (String, ModuleIR DATA) -> Convert (Vect y (String, ChannelIR DATA))
    convertKVs [] = Right Nil
    convertKVs ((l,x) :: xs) =
     do x' <- convert x
        rest <- convertKVs xs
        pure ((l,x')::rest)

convert (MChan x) =
  do x' <- convert x
     pure (CChan x')

convert (MIDX x s y) =
  do s' <- convert s
     y' <- convert y
     pure (CIDX x s' y')

convert (MConn cname y ps) =
    do c <- convert cname
       i <- mkConn y c
       rest <- convPorts c ps
       pure (CSeq i rest)
  where
    convModule : ChannelIR MODULE -> Convert (ChannelIR MODULE)
    convModule m@(CRef x MODULE) = Right m
    convModule (CLet x z w) = Left (NotSupposedToHappen (Just "convModule CIR let"))
    convModule (CSeq x z)   = Left (NotSupposedToHappen (Just "convModule CIR CSeq"))
    convModule (CModule xs) = Left (NotSupposedToHappen (Just "convModule CIR CMod"))

    convPort : ModuleIR PORT -> Convert (ChannelIR MODULE, String)
    convPort (MRef name PORT) = Left (NotSupposedToHappen (Just "convPort CIR Ref"))
    convPort (MLet name beThis inThis) = Left (NotSupposedToHappen (Just "convPort CIR Let"))
    convPort (MSeq doThis thenThis) = Left (NotSupposedToHappen (Just "convPort CIR Seq"))
    convPort (MPort label dir type) = Left (NotSupposedToHappen (Just "convPort CIR Port"))
    convPort (MIDX label x z) =
      do m' <- convert x
         m'' <- convModule m'
         pure (m'',label)

    mkConn : (p : ModuleIR PORT) -> (c : ChannelIR CHAN) -> Convert (ChannelIR CONN)
    mkConn p c =
      do (m,l) <- convPort p
         pure (CModuleInst m [(l,c)])

    convPorts : (c : ChannelIR CHAN) -> (outs : Vect (S n) (ModuleIR PORT)) -> Convert (ChannelIR CONN)
    convPorts c (x :: []) = mkConn x c
    convPorts c (x :: (z :: xs)) =
      do con <- mkConn x c
         rest <- convPorts c (z::xs)
         pure (CSeq con rest)

export
covering
runConvert : ModuleIR type -> Convert (ChannelIR type)
runConvert = convert
