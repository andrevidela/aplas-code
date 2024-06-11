module Data.Sigma

import Data.Ops

||| Dependent pairs
public export
record Σ (a : Type) (b : a -> Type) where
  constructor (##)
  ||| First projection of sigma
  π1 : a
  ||| Second projection of sigma
  π2 : b π1

%pair Σ π1 π2

public export
record SigEq (a, b : Σ f s) where
  constructor MkSigEq
  fstEq : a.π1 === b.π1
  sndEq : a.π2 === replace {p = s} (sym fstEq) b.π2

export
0 sigEqToEq : SigEq a b -> a === b
sigEqToEq {a = _ ## _} {b = _ ## _} (MkSigEq Refl Refl) = Refl

