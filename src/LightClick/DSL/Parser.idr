||| Construct an raw syntax tree instance from a list of tokens.
|||
||| Module    : Parser.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module LightClick.DSL.Parser

import        Data.Vect
import        Data.List
import        Data.List1
import        Data.String
import        Data.Maybe

import public Text.Lexer
import public Text.Parser

import Toolkit.Data.List.View.PairWise

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import        Language.SystemVerilog.Gates

import        LightClick.Core
import        LightClick.Types.Direction
import        LightClick.Types.Sensitivity
import        LightClick.Types.WireType
import        LightClick.Types.Necessity

import        LightClick.DSL.AST

import public LightClick.DSL.Lexer
import        LightClick.DSL.Parser.API

%default total

||| Denotes the two style of port delcarations.
|||
data TypeStyle
  = ||| Label then type.
    HASKELL
  | ||| Type then label.
    SYSV

var : Rule AST
var = do
  s <- Toolkit.location
  n <- name
  e <- Toolkit.location
  pure (Ref (newFC s e) n)

logic : Rule AST
logic = do
  st <- Toolkit.location
  keyword "logic"
  end <- Toolkit.location
  pure (DataLogic (newFC st end))

type__ : Rule AST
type__ = logic <|> var

array : Rule AST
array = do
  s <- Toolkit.location
  ty <- type__
  idx <- braces natLit
  e <- Toolkit.location
  pure (DataArray (newFC s e) ty idx)

mutual
  ascrip : Rule (String, AST)
  ascrip = do
    n <- name
    symbol ":"
    ty <- type_
    pure (n,ty)

  struct : Rule AST
  struct = do
    s <- Toolkit.location
    keyword "struct"
    kvs <- brackets $ commaSepBy1V ascrip
    e <- Toolkit.location
    pure (DataStruct (newFC s e) (snd kvs))

  union : Rule AST
  union = do
    s <- Toolkit.location
    keyword "union"
    kvs <- brackets $ commaSepBy1V ascrip
    e <- Toolkit.location
    pure (DataUnion (newFC s e) (snd kvs))

  enum : Rule AST
  enum
    = do s <- Toolkit.location
         keyword "enum"
         kvs <- brackets $ commaSepBy1V name
         e <- Toolkit.location
         pure (DataEnum (newFC s e) (snd kvs))

  type_ : Rule AST
  type_ = array <|> struct <|> union <|> enum <|> type__

typeDef : Rule (FileContext, String, AST)
typeDef = do
  d <- optional doc
  s <- Toolkit.location
  n <- name
  symbol "="
  decl <- type_
  e <- Toolkit.location
  pure (newFC s e, n, decl)

necessity : Rule Necessity
necessity
    = do {keyword "required"; pure Required}
  <|> do {keyword "optional";      pure Optional}

direction : Rule Direction
direction = do {keyword "inout";  pure INOUT}
        <|> do {keyword "output"; pure OUT}
        <|> do {keyword "input"; pure IN}

sensitivity : Rule Sensitivity
sensitivity = do {keyword "high";  pure High}
          <|> do {keyword "low"; pure Low}
          <|> do {keyword "rising"; pure Rising}
          <|> do {keyword "falling"; pure Falling}
          <|> do {keyword "insensitive"; pure Insensitive}

wireType : Rule Wire
wireType = do {keyword "general";  pure General}
       <|> do {keyword "data"; pure Data}
       <|> do {keyword "address"; pure Address}
       <|> do {keyword "clock"; pure Clock}
       <|> do {keyword "reset"; pure Reset}
       <|> do {keyword "control"; pure Control}
       <|> do {keyword "interrupt"; pure Interrupt}
       <|> do {keyword "info"; pure Info}


portHaskellStyle : Rule AST
portHaskellStyle
  = do st <- Toolkit.location
       com <- optional doc
       label <- name
       symbol ":"
       t <- type_
       c <- option General wireType
       d <- direction
       s <- option Insensitive sensitivity
       n <- option Required    necessity
       e <- Toolkit.location
       pure (Port (newFC st e) label d s c n t)

portSystemVerilogStyle : Rule AST
portSystemVerilogStyle
  = do st <- Toolkit.location
       com <- optional doc
       n <- option Required necessity
       d <- direction
       s <- option Insensitive sensitivity
       c <- option General wireType
       t <- type_
       label <- name
       e <- Toolkit.location
       pure (Port (newFC st e) label d s c n t)

port : TypeStyle -> Rule AST
port HASKELL = portHaskellStyle
port SYSV    = portSystemVerilogStyle

moduleDef : TypeStyle -> Rule (FileContext, String, AST)
moduleDef style
  = do ds <- optional doc
       d <- Toolkit.location
       n <- name
       symbol "="
       s <- Toolkit.location
       keyword "module"
       res <- brackets $ commaSepBy1V (port style)
       e <- Toolkit.location
       pure (newFC d e, n, ModuleDef (newFC s e) (snd res))

idx : Rule AST
idx = do
  s <- Toolkit.location
  m <- var
  n <- braces name
  e <- Toolkit.location
  pure (Index (newFC s e) m n)

ref : Rule AST
ref = idx

connect : Rule AST
connect
    = do s <- Toolkit.location
         l <- ref
         arrow
         r <- ref
         e <- Toolkit.location
         pure (newConn s e l r)
  where
    newConn : (s,e : Location)
           -> (l,r : AST)
           -> AST
    newConn s e = Connect (newFC s e)

fanout : Rule AST
fanout = do
  s <- Toolkit.location
  i  <- ref
  arrow
  fs <- brackets $ commaSepBy2V ref
  e <- Toolkit.location
  pure (FanOut (newFC s e) i (snd fs))

mux : Rule AST
mux = do
  s <- Toolkit.location
  fs <- brackets $ commaSepBy2V ref
  symbol "-"
  ctrl <- parens ref
  arrow
  o <- ref
  e <- Toolkit.location
  pure (Mux (newFC s e) (snd fs) ctrl o)

not : Rule AST
not = do s <- Toolkit.location
         i <- ref
         symbol "!"
         o <- ref
         e <- Toolkit.location
         pure (NOT (newFC s e) i o)

gateType : Rule TyGateComb
gateType = do {symbol "&"; pure AND}
       <|> do {symbol "|"; pure IOR}
       <|> do {symbol "+"; pure XOR}

gateArrow : Rule TyGateComb
gateArrow
  = do symbol "-"
       symbol "["
       g <- gateType
       symbol "]"
       arrow
       pure g

gate : Rule AST
gate = do s <- Toolkit.location
          fs <- brackets $ commaSepBy2V ref
          ty <- gateArrow
          o <- ref
          e <- Toolkit.location
          pure (GATE (newFC s e) ty (snd fs) o)

conns : Rule (List1 AST)
conns
    = some (conn <* symbol ";")
  where
    conn : Rule  AST
    conn = not <|> mux <|> fanout <|> gate <|> connect

types : Rule ( List1 (FileContext, String, AST))
types = do
  keyword "types"
  some (typeDef <* symbol ";")

design : Rule AST
design = do
   ds <- optional (many doc)
   keyword "model"
   keyword "lightclick"
   tyStyleDecl <- optional (do {keyword "verilog"; pure SYSV})
   let typeStyle = fromMaybe HASKELL tyStyleDecl
   ts <- optional types
   (keyword "modules")
   ms <- some (moduleDef typeStyle <* symbol ";")
   (keyword "connections")
   cs <- conns
   start <- Toolkit.location
   eoi
   let cs' = foldr Seq (End (newFC start start)) (forget cs)
   let ms' = foldr buildBind cs' (forget ms)
   let res = foldr buildBind ms' $ maybe Nil forget ts
   pure res
  where
   buildBind : (FileContext, String, AST) -> AST -> AST
   buildBind (fc, n,e) body = (Bind fc n e body)


||| Construct an raw syntax tree instance from a list of tokens.
export
fromFile : (fname : String)
                 -> LightClick AST
fromFile fname
  = do res <- parseFile (FileError fname)
                        LightClickLexer
                        design
                        fname
       pure (setFileName fname res)

-- [ EOF ]
