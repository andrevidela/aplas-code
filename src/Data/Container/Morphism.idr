module Data.Container.Morphism

import public Data.Container

import Control.Order
import Control.Relation

||| A container morphism
public export
record (=%>) (c1, c2 : Container) where
  constructor (<|)
  fwd : c1.req -> c2.req
  bwd : (x : c1.req) -> c2.res (fwd x) -> c1.res x

%pair (=%>) fwd bwd

||| Identity of container morphisms
public export
identity : a =%> a
identity = id <| (\_ => id)

public export
(⨾) : a =%> b -> b =%> c -> a =%> c
(⨾) x y = (y.fwd . x.fwd) <| (\z => x.bwd z . y.bwd (x.fwd z))

public export
embed : {0 a : Type} -> {0 b : a -> Type} -> (f : (x : a) -> b x) ->
    ((!>) a b) =%> CUnit
embed f = (\_ => ()) <| (\x, _ => f x)

public export
extract : ((!>) a b) =%> CUnit -> (x : a) -> b x
extract c x = c.bwd x ()

public export
unit : CUnit ⊗ CUnit =%> CUnit
unit =
  (\_ => ()) <|
  (\_, _ => () && ())

public export
dia : a + a =%> a
dia =
  dia <|
  (\case (+> r) => id
         (<+ l) => id)

public export
Reflexive Container (=%>) where
  reflexive = identity

public export
Transitive Container (=%>) where
  transitive = (⨾)

public export
Preorder Container (=%>) where
