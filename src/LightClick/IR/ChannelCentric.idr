||| A channel centric IR.
|||
||| Module    : ChannelCentric.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Chnnel centric IRs follow the SystemVerilog approach to hardware description.
||| First, the channels between modules are declared.
||| Second, the channel endpoints are then used to instantiate modules.
|||
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
  CRef : (name : String)
      -> (type : TyIR)
              -> ChannelIR type

  CLet : {term   : TyIR}
      -> (bind   : String)
      -> (this   : ChannelIR term)
      -> (inThis : ChannelIR expr)
                -> ChannelIR expr

  CSeq  : {a,b  : TyIR}
       -> (this : ChannelIR a)
       -> (that : ChannelIR b)
               -> ChannelIR b

  CEnd : ChannelIR UNIT

  CPort : String
       -> Direction
       -> Necessity
       -> ChannelIR DATA
       -> ChannelIR PORT

  CModule : {n    : Nat}
         -> (pots : Vect (S n) (ChannelIR PORT))
                 -> ChannelIR MODULE

  CDataLogic : ChannelIR DATA

  CDataEnum : {n      : Nat}
           -> (fields : Vect (S n) String)
                     -> ChannelIR DATA

  CDataArray : (type : ChannelIR DATA)
            -> (size : Nat)
                    -> ChannelIR DATA

  CDataStruct : {n      : Nat}
             -> (fields : Vect (S n)
                               (Pair String
                                     (ChannelIR DATA)))
                        -> ChannelIR DATA

  CDataUnion : {n      : Nat}
            -> (fields : Vect (S n)
                              (Pair String
                                    (ChannelIR DATA)))
                      -> ChannelIR DATA

  ||| don't exist in the normal form, required for mapping MIDX to
  ||| something for coverage...
  CIDX : (label : String)
      -> (m     : ChannelIR MODULE)
               -> ChannelIR PORT

  CChan : (type : ChannelIR DATA)
               -> ChannelIR CHAN

  CNoOp : ChannelIR CHAN

  CModuleInst : {n         : Nat}
             -> (mname     : ChannelIR MODULE)
             -> (endpoints : Vect (S n)
                                  (Pair String
                                        (ChannelIR CHAN)))
                           -> ChannelIR CONN

  CNot : (to, from : ChannelIR CHAN)
                  -> ChannelIR GATE

  CGate : {n    : Nat}
       -> (kind : TyGateComb)
       -> (to   : ChannelIR CHAN)
       -> (from : Vect (S (S n)) (ChannelIR CHAN))
               -> ChannelIR GATE

mutual
  namespace Port

    %inline
    module_ : ChannelIR MODULE
           -> LightClick (ChannelIR MODULE)

    module_ m@(CRef x MODULE)
      = pure m

    module_ (CLet x z w)
      = throw (NotSupposedToHappen (Just "module_ CIR let"))

    module_ (CSeq x z)
      = throw (NotSupposedToHappen (Just "module_ CIR CSeq"))

    module_ (CModule xs)
      = throw (NotSupposedToHappen (Just "module_ CIR CMod"))

    export
    convert : ModuleIR PORT
           -> LightClick (ChannelIR MODULE, String)

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
             m'' <- module_ m'
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
    convert c (x :: [])
      = mkConn x c

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

  convert (MPort x y n z)
    = do z' <- convert z
         pure $ CPort x y n z'

  convert (MModule {n} x)
    = do xs <- traverse convert x
         pure $ CModule xs

  convert MDataLogic
    = pure CDataLogic

  convert (MDataEnum xs)
    = pure (CDataEnum xs)

  convert (MDataArray x k)
    = do x' <- convert x
         pure $ CDataArray x' k

  convert (MDataStruct xs)
    = do xs' <- traverse (\(l,x) => do {x' <- convert x; pure (l, x')}) xs
         pure $ CDataStruct xs'

  convert (MDataUnion xs)
    = do xs' <- traverse (\(l,x) => do {x' <- convert x; pure (l,x')}) xs
         pure $ CDataUnion xs'

  convert (MChan x)
    = do x' <- convert x
         pure (CChan x')

  convert (MIDX x s)
    = do s' <- convert s
         pure (CIDX x s')

  convert (MConn cname y ps)
    = do c <- convert cname
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

  convert (MNoOp idx)
    = mkConn idx CNoOp

||| Transform the module centric representation into a channelise
||| variant.
export
channelise : (m : ModuleIR type)
               -> LightClick (ChannelIR type)
channelise = convert

-- [ EOF ]
