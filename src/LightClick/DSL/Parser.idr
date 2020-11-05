module LightClick.DSL.Parser

import        Data.Vect
import        Data.List
import        Data.Strings
import        Data.Maybe

import public Text.Lexer
import public Text.Parser

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import        Language.SystemVerilog.Gates

import        LightClick.Types.Direction
import        LightClick.Types.Sensitivity
import        LightClick.Types.WireType

import        LightClick.DSL.AST

import public LightClick.DSL.Lexer

%default total

data TypeStyle = HASKELL | SYSV

eoi : RuleEmpty Token ()
eoi = eoi isEOI

  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

symbol : String -> Rule Token ()
symbol str
  = terminal ("Expected Symbol '" ++ str ++ "'")
             (\x => case tok x of
                           Symbol s => if s == str then Just ()
                                                   else Nothing
                           _ => Nothing)


keyword : String -> Rule Token ()
keyword str
  = terminal ("Expected Keyword '" ++ str ++ "'")
               (\x => case tok x of
                           Keyword s => if s == str then Just ()
                                                    else Nothing
                           _ => Nothing)


natLit : Rule Token Nat
natLit = terminal "Expected nat literal"
             (\x => case tok x of
                         LitNat i => Just i
                         _ => Nothing)

strLit : Rule Token String
strLit = terminal "Expected string literal"
             (\x => case tok x of
                         LitStr s => Just s
                         _ => Nothing)

identifier : Rule Token String
identifier
  = terminal "Expected Identifier"
             (\x => case tok x of
                                ID str => Just str
                                _ => Nothing)

doc : Rule Token (List String)
doc = some docString
  where
    docString : Rule Token String
    docString = terminal "Documentation String"
                         (\x => case tok x of
                                     Documentation doc => Just doc
                                     _ => Nothing)

name : Rule Token String
name = identifier

arrow : Rule Token ()
arrow = symbol "->"

braces : Inf (Rule Token a)
      -> Rule Token a
braces = between (symbol "[")
                 (symbol "]")

brackets : Inf (Rule Token a )
        -> Rule Token a
brackets = between (symbol "{") (symbol "}")

parens : Inf (Rule Token a)
      -> Rule Token a
parens = between (symbol "(") (symbol ")")

commaSepBy1 : Rule Token a -> Rule Token (xs : List a ** NonEmpty xs)
commaSepBy1 = sepBy1' (symbol ",")


sepBy1V : (sep : Rule Token b)
       -> (p : Rule Token a)
       -> Rule Token (n ** Vect (S n) a)
sepBy1V sep p = do {x <- p; xs <- many (sep *> p); pure (_ ** fromList $ x::xs)}

sepBy2V : (sep : Rule Token b)
       -> (p : Rule Token a)
       -> Rule Token (n ** Vect (S (S n)) a)
sepBy2V sep p = do {x <- p; sep; y <- p; rest <- many (sep *> p); pure (_ ** fromList $ x::y::rest)}

commaSepBy1V : (p : Rule Token a) -> Rule Token (n ** Vect (S n) a)
commaSepBy1V = sepBy1V (symbol ",")

commaSepBy2V : (p : Rule Token a) -> Rule Token (n ** Vect (S (S n)) a)
commaSepBy2V = sepBy2V (symbol ",")

var : Rule Token AST
var = do
  s <- location
  n <- name
  e <- location
  pure (Ref (newFC s e) n)

logic : Rule Token AST
logic = do
  st <- location
  keyword "logic"
  end <- location
  pure (DataLogic (newFC st end))

type__ : Rule Token AST
type__ = logic <|> var

array : Rule Token AST
array = do
  s <- location
  ty <- type__
  idx <- braces natLit
  e <- location
  pure (DataArray (newFC s e) ty idx)

mutual
  ascrip : Rule Token (String, AST)
  ascrip = do
    n <- name
    symbol ":"
    ty <- type_
    pure (n,ty)

  struct : Rule Token AST
  struct = do
    s <- location
    keyword "struct"
    kvs <- brackets $ commaSepBy1V ascrip
    e <- location
    pure (DataStruct (newFC s e) (snd kvs))

  union : Rule Token AST
  union = do
    s <- location
    keyword "union"
    kvs <- brackets $ commaSepBy1V ascrip
    e <- location
    pure (DataUnion (newFC s e) (snd kvs))

  type_ : Rule Token AST
  type_ = array <|> struct <|> union <|> type__

typeDef : Rule Token (FileContext, String, AST)
typeDef = do
  optional doc
  s <- location
  n <- name
  symbol "="
  decl <- type_
  e <- location
  pure (newFC s e, n, decl)

direction : Rule Token Direction
direction = do {keyword "inout";  pure INOUT}
        <|> do {keyword "output"; pure OUT}
        <|> do {keyword "input"; pure IN}

sensitivity : Rule Token Sensitivity
sensitivity = do {keyword "high";  pure High}
          <|> do {keyword "low"; pure Low}
          <|> do {keyword "rising"; pure Rising}
          <|> do {keyword "falling"; pure Falling}
          <|> do {keyword "insensitive"; pure Insensitive}

wireType : Rule Token Wire
wireType = do {keyword "general";  pure General}
       <|> do {keyword "data"; pure Data}
       <|> do {keyword "address"; pure Address}
       <|> do {keyword "clock"; pure Clock}
       <|> do {keyword "reset"; pure Reset}
       <|> do {keyword "control"; pure Control}
       <|> do {keyword "interrupt"; pure Interrupt}
       <|> do {keyword "info"; pure Info}


portHaskellStyle : Rule Token AST
portHaskellStyle
  = do st <- location
       optional doc
       label <- name
       symbol ":"
       t <- type_
       c <- wireType
       d <- direction
       s <- sensitivity
       e <- location
       pure (Port (newFC st e) label d s c t)

portSystemVerilogStyle : Rule Token AST
portSystemVerilogStyle
  = do st <- location
       optional doc
       d <- direction
       s <- sensitivity
       c <- wireType
       t <- type_
       label <- name
       e <- location
       pure (Port (newFC st e) label d s c t)

port : TypeStyle -> Rule Token AST
port HASKELL = portHaskellStyle
port SYSV    = portSystemVerilogStyle

moduleDef : TypeStyle -> Rule Token (FileContext, String, AST)
moduleDef style
  = do optional doc
       d <- location
       n <- name
       symbol "="
       s <- location
       keyword "module"
       res <- brackets $ commaSepBy1V (port style)
       e <- location
       pure (newFC d e, n, ModuleDef (newFC s e) (snd res))

idx : Rule Token AST
idx = do
  s <- location
  m <- var
  n <- braces name
  e <- location
  pure (Index (newFC s e) m n)

ref : Rule Token AST
ref = idx

connect : Rule Token AST
connect = do
  s <- location
  l <- ref
  arrow
  r <- ref
  e <- location
  pure (Connect (newFC s e) l r)

fanout : Rule Token AST
fanout = do
  s <- location
  i  <- ref
  arrow
  fs <- brackets $ commaSepBy2V ref
  e <- location
  pure (FanOut (newFC s e) i (snd fs))

mux : Rule Token AST
mux = do
  s <- location
  fs <- brackets $ commaSepBy2V ref
  symbol "-"
  ctrl <- parens ref
  arrow
  o <- ref
  e <- location
  pure (Mux (newFC s e) (snd fs) ctrl o)

not : Rule Token AST
not = do s <- location
         i <- ref
         symbol "!"
         o <- ref
         e <- location
         pure (NOT (newFC s e) i o)

gateType : Rule Token TyGateComb
gateType = do {symbol "&"; pure AND}
       <|> do {symbol "|"; pure IOR}
       <|> do {symbol "+"; pure XOR}

gate : Rule Token AST
gate = do s <- location
          fs <- brackets $ commaSepBy2V ref
          ty <- gateType
          o <- ref
          e <- location
          pure (GATE (newFC s e) ty (snd fs) o)

conn : Rule Token AST
conn = not <|> mux <|> fanout <|> connect <|> gate

types : Rule Token (xs : List (FileContext, String, AST) ** NonEmpty xs)
types = do
  keyword "types"
  some' (typeDef <* symbol ";")

export
design : Rule Token AST
design = do
   optional (many doc)
   keyword "model"
   keyword "lightclick"
   tyStyleDecl <- optional (do {keyword "verilog"; pure SYSV})
   let typeStyle = fromMaybe HASKELL tyStyleDecl
   ts <- optional types
   (keyword "modules")
   ms <- some'  (moduleDef typeStyle <* symbol ";")
   (keyword "connections")
   cs <- some' (conn <* symbol ";")
   Parser.eoi
   let cs' = foldr Seq End (fst cs)
   let ms' = foldr buildBind cs' (fst ms)
   let res = foldr buildBind ms' $ maybe Nil fst ts
   pure res
  where
   buildBind : (FileContext, String, AST) -> AST -> AST
   buildBind (fc, n,e) body = (Bind fc n e body)

export
parseClickStr : {e   : _}
             -> (rule : Grammar (TokenData Token) e ty)
             -> (str : String)
             -> Either (Run.ParseError Token) ty
parseClickStr rule str = parseString LightClickLexer rule str

export
parseClickFile : {e     : _}
              -> (rule  : Grammar (TokenData Token) e ty)
              -> (fname : String)
                       -> IO (Either (Run.ParseError Token) ty)
parseClickFile = parseFile LightClickLexer

export
parseClickDesignFile : (fname : String)
                    -> IO (Either (Run.ParseError Token) AST)
parseClickDesignFile = parseFile LightClickLexer design


-- [ EOF ]
