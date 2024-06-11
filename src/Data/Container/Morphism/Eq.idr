module Data.Container.Morphism.Eq

import public Proofs.Congruence
import public Proofs.Extensionality

import public Control.Relation
import public Control.Order

import Data.Container.Morphism
import Data.Iso

public export infix 0 `DepLensEq`

||| Two container morphisms are equal if their mapping on shapes are equal and their
||| mapping on positions are equal.
public export
record DepLensEq (a, b : dom =%> cod) where
  constructor MkDepLensEq
  0 eqFwd : (v : dom.req) -> a.fwd v === b.fwd v
  0 eqBwd : (v : dom.req) -> (y : cod.res (a.fwd v)) ->
          let 0 p1 : dom.res v
              p1 = a.bwd v y
              0 p2 : dom.res v
              p2 = b.bwd v (replace {p = cod.res} (eqFwd v) y)
          in p1 === p2
export
0 depLensEqToEq : DepLensEq a b -> a === b
depLensEqToEq {a = (fwd1 <| bwd1)} {b = (fwd2 <| bwd2)} (MkDepLensEq eqFwd eqBwd) =
  cong2Dep (<|) (funExt eqFwd) (funExtDep $ \x => funExt $ \y => eqBwd x y)

public export
Transitive (dom =%> cod) DepLensEq where
  transitive a b = MkDepLensEq (\v => transitive (a.eqFwd v) (b.eqFwd v))
      (\v, w => transitive
           (a.eqBwd v w)
           (b.eqBwd v (replace {p = cod.res} (a.eqFwd v) w)))

public export
Reflexive (dom =%> cod) DepLensEq where
  reflexive = MkDepLensEq (\_ => Refl) (\_, _ => Refl)

public export
Preorder (dom =%> cod) DepLensEq where

||| An isomorphism of container morphisms
public export
ContIso : (x, y : Container) -> Type
ContIso = GenIso Container (=%>) DepLensEq
