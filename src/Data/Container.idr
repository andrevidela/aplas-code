module Data.Container

import public Data.Product
import public Data.Coproduct
import public Data.Sigma
import public Data.Category.Ops

import Proofs.Congruence
import Proofs.Extensionality

%default total

||| A container is a product of a shape and a set of positions indexed by that shape
||| They can be used to describe data types
public export
record Container where
  constructor (!>)
  ||| Shapes
  req : Type
  ||| Positions
  res : req -> Type

%pair Container req res

||| A constructor for containers where the responses do not depend on the requests
public export
(:-) : Type -> Type -> Container
(:-) x y = (!>) x (const y)

||| The unit for containers
public export
CUnit : Container
CUnit = Unit :- Unit

||| The neutral for composition
public export
CNeutral : Container
CNeutral = Unit :- Void

||| The coproduct on containers, neutral is CVoid
public export
(+) : (c1, c2 : Container) -> Container
(+) c1 c2 = (!>) (c1.req + c2.req) (choice c1.res c2.res)

||| The tensor on containers, neutral element is CUnit
public export
(⊗) : (c1, c2 : Container) -> Container
(⊗) c1 c2 = (x : c1.req * c2.req) !> c1.res x.π1 * c2.res x.π2

||| Extension of a container as a functor
public export
record Ex (cont : Container) (ty : Type) where
  constructor MkEx
  ex1 : cont.req
  ex2 : cont.res ex1 -> ty

%pair Ex ex1 ex2

public export
record ExEq {a : Container} {b : Type} (c1, c2 : Ex a b) where
  constructor MkExEq
  pex1 : c1.ex1 === c2.ex1
  pex2 : (v : a.res c1.ex1) ->
         let 0 b1, b2 : b
             b1 = c1.ex2 v
             b2 = c2.ex2 (rewrite__impl a.res (sym pex1) v)
          in b1 === b2

public export
0 exEqToEq : ExEq c1 c2 -> c1 === c2
exEqToEq {c1 = MkEx x1 x2} {c2 = MkEx y1 y2} (MkExEq x y) =
  cong2Dep MkEx x (funExt $ y)
