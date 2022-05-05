||| A Soundness check to ensure the model has a 'normal form'.
|||
||| Module    : Soundness.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Our model is sound if we can compute a well-formed graph.
|||
||| We translate each construct in our model to nodes and vertices
||| from a graph, and reason about the expected and actual degrees in
||| the graph. The model is sound if the expected and actual degrees
||| are the same.
|||
module LightClick.Soundness

import Decidable.Equality

import Data.String
import Data.Nat
import Data.Fin
import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Informative

import Toolkit.Data.DVect

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.Valid

import Toolkit.DeBruijn.Environment

import Language.SystemVerilog.Gates

import LightClick.Core
import LightClick.Types
import LightClick.Terms

%default total

-- [ Helper constructs ]

||| Need to associate a named port with the Vertex.
data Thing : String -> Type where
  Vertex : Vertex String -> Thing x

ident : Thing x  -> Nat
ident (Vertex y) = ident y

Things : {n : Nat} -> Vect n String -> Type
Things {n} = DVect String Thing n

toList : Things names -> List (Vertex String)
toList [] = []
toList ((Vertex x) :: rest) = x :: toList rest

-- [ Interpretation of Types ]

||| Interpret our types to constructs ina graph.
public export
Interp : {m : MTy} -> Ty m -> Type
Interp {m = (PORT x)} _
  = Thing x

Interp {m = UNIT} _
  = Unit

Interp {m = (MODULE xs)} _
  = Things xs

Interp {m = CONN} _
  = Unit

Interp {m = DATA} _
  = Unit

Interp {m = GATE} _
  = Unit

-- [ Interpretation Environments and Result Validity ]

data Value : Item -> Type where
  V : Erase i (m ** ty) -> (Interp ty) -> Value i

Env : List Item -> Type
Env = Env Item Value

data Result : {m : MTy}
           -> (context : List Item)
           -> (type    : Ty m)
                      -> Type
  where
    R : (counter : Nat)
     -> (env     : Env new)
     -> (graph   : Graph String)
     -> (result  : Interp type)
                -> Result new type

public export
data Valid : (res  : Result ctxt TyUnit)
                  -> Type
  where
    D : (g   : Graph String)
            -> ValidGraph g
            -> Valid (R c e g r)

isValid : (r : Result ctxt TyUnit)
            -> DecInfo (Graph String, HasExactDegree.Error String)
                       (Valid r)
isValid (R counter env graph result) with (validGraph graph)
  isValid (R counter env (MkGraph vs es) result) | (Yes (IsValid x))
    = Yes (D (MkGraph vs es) (IsValid x))
  isValid (R counter env graph result) | (No msg contra)
    = No (graph,msg)
         (\(D graph prf) => contra prf)

||| Transform terms into a graph.
|||
interp : {old     : Context}
      -> (env     : Env old)
      -> (counter : Nat)
      -> (graph   : Graph String)
      -> (term    : Term old type new)
                 -> (Result new type)

-- [ Helper Functions to return the correct results ]

data Fields : (ctxt : List Item)

                   -> Type
  where
    FIELD : {ctxt  : Context}
         -> (counter : Nat)
         -> (env   : Env ctxt)
         -> (graph : Graph String)
                -> Fields ctxt

fields : {old     : Context}
      -> (env     : Env old)
      -> (counter : Nat)
      -> (graph   : Graph String)
      -> (fs      : Fields old n types new)
                 -> Fields new
fields e c g Empty
  = FIELD c e g

fields e c g (Extend s tm rest)
  = let R c1 e1 g1 x = interp e c g tm
    in let FIELD c2 e2 g2 = fields e1 c1 g1 rest
    in FIELD c2 e2 g2


data Fan : (ctxt  : List Item)
        -> (n     : Nat)
        -> (ns    : Vect n String)
                 -> Type
  where
    FAN : {ctxt  : Context}
       -> (counter : Nat)
       -> (env   : Env ctxt)
       -> (graph : Graph String)
       -> (ports : DVect String Thing n names)
                -> Fan ctxt n names

fan : {old     : Context}
   -> (env     : Env old)
   -> (counter : Nat)
   -> (graph   : Graph String)
   -> {names   : Vect n String}
   -> {types   : DVect String (Ty . PORT) n names}
   -> (fs      : Fan old n types new)
              -> Fan new n names
fan env c g Empty
  = FAN c env g Nil

fan env c g (Extend term rest)
  = let R c1 e1 g1 x = interp env c g term
    in let FAN c2 e2 g2 xs = fan e1 c1 g1 rest
    in FAN c2 e2 g2 (x::xs)

data Ports : (ctxt : List Item)
          -> (n    : Nat)
          -> (ns   : Vect n String)
                  -> Type

  where
   PORTS : {ctxt : Context}
        -> (c    : Nat)
        -> (env  : Env ctxt)
        -> (g    : Graph String)
        -> (ps   : DVect String Thing n names)
                -> Ports ctxt n names

ports : {old     : Context}
     -> (env     : Env old)
     -> (counter : Nat)
     -> (graph   : Graph String)
     -> {names   : Vect n String}
     -> {types   : DVect String (Ty . PORT) n names}
     -> (fs      : Ports old n types new)
                -> Ports new n names
ports env c g Empty
  = PORTS c env g Nil

ports env c g (Extend port later)
  = let R c1 e1 g1 x = interp env c g port
    in let PORTS c2 e2 g2 xs = ports e1 c1 g1 later
    in PORTS c2 e2 g2 (x::xs)

data FreeVar : (ctxt : List Item)
            -> (type : Ty m)
                    -> Type
  where
    FREEVAR : {ctxt : Context}
           -> (env  : Env ctxt)
           -> (val  : Interp type)
                   -> FreeVar ctxt type

read : (env : Env old)
    -> (prf : FreeVar (I type usage) old)
    -> (use : UseFreeVar old prf new)
           -> FreeVar new type
read ((V E y) :: rest) (Here (Free prfU)) (UH prfU)
  = FREEVAR (V E y :: rest) y

read (elem :: rest) (There later) (UT x) with (read rest later x)
  read (elem :: rest) (There later) (UT x) | (FREEVAR env val)
    = FREEVAR (elem :: env) val


data FreeModule : (ctxt : List Item)
               -> {xs   : Vect (S n) String}
               -> (type : Ty (MODULE xs))
                       -> Type
  where
    FREEMODULE : {ctxt : Context}
              -> {xs   : Vect (S n) String}
              -> {type : Ty (MODULE xs)}
              -> (env  : Env ctxt)
              -> (val  : Interp type)
                      -> FreeModule ctxt type

readModule : (env : Env old)
          -> {xs   : Vect (S n) String}
          -> {type : Ty (MODULE xs)}
          -> {usage : Usage (MODULE xs)}
          -> (prf : FreePort label (I type usage) old)
          -> (use : UseFreePort old prf new)
                 -> FreeModule new type
readModule ((V E y) :: rest) (Here (IFP (FE idx prfU))) (UH idx prfU)
  = FREEMODULE ((V E y) :: rest)
               y

readModule (elem :: rest) (There later) (UT x) with (readModule rest later x)
  readModule (elem :: rest) (There later) (UT x) | (FREEMODULE env val)
    = FREEMODULE (elem :: env) val


findPort : {ms : DVect String (Ty . PORT) n names}
        -> (prf : DVect.HasPortNamed l ms port)
        -> (things : DVect String Thing n names)
                  -> Thing l
findPort (Here x) (ex :: rest) = ex
findPort (There later) (ex :: rest)
  = findPort later rest

getPort : {type : Ty (MODULE xs)}
       -> {port   : Ty (PORT l)}
       -> (prf    : HasPortNamed l type port)
       -> (this   : FreeModule new type)
                 -> (Env new, Thing l)
getPort (HPN prf) (FREEMODULE env val)
    = let f = findPort prf val
      in (env, f)


-- [ Interpretation Definition ]

{- [ NOTE ]

References get read from the interpretation environment.

-}
interp env c g (Ref fc l prf use)
  = let FREEVAR new val = read env prf use
    in R c new g val

{- [ NOTE ]

Let bindings merge the result of interpreting the bound term and the
resulting scope.

-}
interp env c g (Let fc label this prf newI inThis)

  = let R c1 e1 g1 t = interp env c g this
    in let e2 = extend e1 (V E t)
    in let g2 = merge g g1
    in interp e2 c1 g2 inThis

{- [ NOTE ]

Sequences pass the resulting graph into the next interpretation.

-}
interp env c g (Seq this prf that)
  = let R c1 e1 g1 x = interp env c g this
    in interp e1 c1 g1 that

{- [ NOTE ]

We ignore data type declarations.

-}
interp env c g (DataLogic fc)
  = R c env g MkUnit

interp env c g (DataEnum fc xs)
  = R c env g MkUnit

interp env c g (DataArray fc size x)
  = let R c1 e1 g1 MkUnit = interp env c g x
    in  R c1 e1 g1 MkUnit

interp env c g (DataStruct fc xs)
  = let FIELD c1 e1 g1 = fields env c g xs
    in R c1 e1 g1 MkUnit

interp env c g (DataUnion fc xs)
  = let FIELD c1 e1 g1 = fields env c g xs
    in R c1 e1 g1 MkUnit

{- [ NOTE ]

Ports, which only appear in module declarations, are leaf nodes in a graph.

Specifically:

+ nodes marked OUT   have: IN degree 0, OUT degree 1;
+ nodes marked IN    have: IN degree 1, OUT degree 0;
+ nodes marked INOUT have: IN degree 1, OUT degree 1;

-}
interp env c g (Port fc l d s w n i)
    = let c1 = S c

      in let R c2 e1 g MkUnit = interp env c1 g i

      in let port = buildVertex l d c1

      in R c2 e1 (merge g (fromLists [port] Nil)) (Vertex port)
  where
    buildVertex : String -> Direction -> Nat -> Vertex String
    buildVertex l IN k
      = (catcher ("\{l} catches") k 1)

    buildVertex l OUT k
      = (driver ("\{l} drives") k 1)

    buildVertex l INOUT k
      = (gateway "\{l} both" k 1)

{- [ NOTE ]

Modules are synthetic groupings of nodes.

-}
interp env c g (Module fc ps)
  = let PORTS c1 e1 g1 ps = ports env c g ps
    in R c1 e1 g1 ps

{- [ NOTE ]

Indexing a module returns the specified index.

-}
interp env c g (Index fc mref label prf use getP) with (readModule env prf use)
  interp env c g (Index fc mref label prf use getP) | p with (getPort getP p)
    interp env c g (Index fc mref label prf use getP) | p | (x, y)
      = R c x g y

{- [ NOTE ]

Noops support connecting to optional wires.

We need to make sure the noop is constructed correctly.

For IN/OUT nodes this is simple.
For INOUT nodes we assume that the port is a catcher.

-}
interp env c g (NoOp fc dir term)
    = let c1 = S c

      in let R c2 e2 g1 o = interp env c1 g term
      in let (c3,noop) = buildVertex dir c2

      in let e = buildEdge dir noop o
      in R c3 e2
              (merge g1 (fromLists [noop] [e]))
              MkUnit

  where
    buildVertex : EndpointKind
               -> Nat
               -> (Pair Nat (Vertex String))
    buildVertex DRIVER k
      = MkPair (S k) (driver "noop drives" k 1)

    buildVertex CATCHER k
      = MkPair (S k) (catcher "noop catches" k 1)

    buildVertex BOTH k
      = MkPair (S k) (catcher "noop both but drives" k 1)

    buildEdge : EndpointKind
             -> (noop : Vertex String)
             -> (v    : Thing a)
             -> Edge
    buildEdge DRIVER noop v
      = (ident noop, ident v)

    buildEdge CATCHER noop v
      = (ident v, ident noop)

    buildEdge BOTH noop v
      = (ident noop, ident v)

-- [ Connections ]

{- [ NOTE ]

Direct connections are edges.

-}
interp env c g (Connect fc left right prf)

  = let    R c2 e1 g1 vl = interp env c g left
    in let R c3 e2 g2 vr = interp e1 c2 g1 right

    in let g3 = insertEdge ((ident vl), (ident vr)) g2

    in R c3 e2 g3 MkUnit

{- [ NOTE ]

Fanouts are an explicit split node whose IN degree is one, and out degree matches all the outputs.

-}
interp env c g (FanOut fc input fs prf)
  = let R c1 e1 g1 i = interp env c g input

    in let FAN c2 e2 g2 os = fan e1 c1 g1 fs

    in let c3 = S c2
    in let os' = toList os
    in let fan = node "FANOUT" c3 1 ((length os'))

    in let es = map ((MkPair (ident fan) . ident)) os'

    in let es' = (MkPair (ident i) (ident fan)) :: es

    in let g3 = merge g2 (fromLists [fan] (toList es'))

    in R c3 e2 g3 MkUnit

{- [ NOTE ]

Like fanouts, multiplexers require an explicit join node to connect all the wires together.

The IN degree is one plus (for the control wire) the number of inputs, and the OUT degree is one.

-}
interp env c g (Mux fc fs ctrl output prf)
  = let FAN c1 e1 g1 fs = fan env c g fs
    in let R c2 e2 g2 c = interp e1 c1 g1 ctrl
    in let R c3 e3 g3 o = interp e2 c2 g2 output

    in let c4 = S c3

    in let fs = Soundness.toList fs

    in let mux = node "MUX" c4 (S (length fs)) 1

    in let es' = map (\i => (MkPair (ident i) (ident mux))) fs

    in let es = es' ++  [ MkPair (ident c)   (ident mux)
                        , MkPair (ident mux) (ident o)
                        ]

    in let g4 = merge g3 (fromLists [mux] (toList es))

    in R c4 e3 g4 MkUnit

{- [ NOTE ]

Not gates are analogous to direct connections.

-}
interp env c g (NOT fc left right prf)

  = let c1 = S c

    in let notGate = node "NOT" c1 1 1
    in let R c2 e1 g1 vl = interp env c1 g  left
    in let R c3 e2 g2 vr = interp e1  c2 g1 right

    in let g3 = fromLists [notGate]
                          [ MkPair (ident vl)      (ident notGate)
                          , MkPair (ident notGate) (ident vr)
                          ]
    in R c3 e2 (merge g2 g3) MkUnit

{- [ NOTE ]

Like multiplexers and fanouts, n-ary gates require an explicit node with OUT degree 1, and IN degree the size of the inputs.

-}
interp env c g (GATE fc ty fs output prf)

  = let FAN c1 e1 g1 fs = fan env c g fs
    in let R c2 e2 g2 o = interp e1 c1 g1 output

    in let c4 = S c2

    in let fs = toList fs

    in let mux = node (show ty) c4 (length fs) 1

    in let es' = map (\i => (MkPair (ident i) (ident mux))) fs

    in let es = es' ++  [ MkPair (ident mux) (ident o) ]

    in let g4 = merge g2 (fromLists Nil (toList es))

    in R c4 e2 g4 MkUnit

{- [ NOTE ]

Stop.

-}
interp env c g (End fc x)
  = R c Nil g MkUnit


||| Our model is sound if it is a valid edge bounded graph.
public export
data IsSound : (term : Term Nil TyUnit Nil)
                    -> Type
  where
    IS : (prf : Valid (interp Nil Z (MkGraph Nil Nil) term))
              -> IsSound term

-- [ Helper functions for better diagnostic output ]


Show (Vertex String) where
  show (Node d k j i)
    = show k
      <+> " [label=\""
      <+> show (j,i)
      <+> " "
      <+> d
      <+> "\"];"
  show (Leaf d x k j)
      = show k
        <+> " [label=\""
        <+> withFlow x j
        <+> " "
        <+> d
        <+> "\"];"

    where withFlow : Flow -> Nat -> String
          withFlow f k = show f <+> "(" <+> show k <+>")"

showGraph : Graph String -> String
showGraph (MkGraph nodes edges)
    = unlines $ ["digraph G {"]
                ++
                  map show nodes
                ++
                  map (\(x,y) => unwords [ "\t" <+> show x
                                         , "->"
                                         , show y <+> ";"
                                         ])
                      edges
                ++
                ["}"]


Show DegreeType where
  show I = "IN"
  show O = "OUT"

showErr : (Graph String, HasExactDegree.Error String)
        -> String
showErr (g, MkError vertex kind (MkError vertexID k values))
 = unlines [showGraph g
           , "//because:"
           , "// Vertex " <+> show (ident vertex)
           , "//  has expected degree "
             <+> show k
             <+> " "
             <+> show (values.expected)
           , "//  but we found degree "
             <+> show k
             <+> " "
             <+> show (values.found)
           ]


||| Check to see if the model is sound.
export
isSound : (term : Term Nil TyUnit Nil)
               -> LightClick (IsSound term)
isSound term with (isValid $ interp Nil Z (MkGraph Nil Nil) term)
  isSound term | (Yes prfWhy) = pure (IS prfWhy)
  isSound term | (No msg prfWhyNot)
    = let msg = showErr msg
      in throw (NotSupposedToHappen (Just $ unlines ["Soundness Error", msg]))


-- [ EOF ]
