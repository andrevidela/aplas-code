module Data.Category.Functor

import public Data.Category

%hide Prelude.Functor

%unbound_implicits off

public export
record Functor {0 o1, o2 : Type} (cat1 : Category o1) (cat2 : Category o2) where
  constructor MkFunctor

  -- a way to map objects
  F : o1 -> o2

  -- a way to map morphisms
  -- For each morphism in cat1 between objects a and b
  -- we get a morphism in cat2 between the corresponding objects a and b
  -- but mapped to their counterparts in cat2
  F' : (0 a, b : o1) -> a ~> b -> F a ~> F b

  -- mapping the identity morphism in cat1 results in the identity morphism in cat2
  0 presId : (v : o1) -> F' v v (id cat1 v) = id cat2 (F v)

  -- composition of hom-sets
  0 presComp : (a, b, c : o1) ->
               (f : a ~> b) ->
               (g : b ~> c) ->
               F' a c ((|:>) cat1 {a, b, c} f g)
             = ((|:>) cat2) {a=F a, b=F b, c=F c} (F' a b f) (F' b c g)

-- composition of functors
public export
(*>) : {0 o1, o2, o3 : Type} -> {0 a : Category o1} -> {0 b : Category o2} -> {0 c : Category o3} ->
      Functor a b -> Functor b c -> Functor a c
(*>) f1 f2 = MkFunctor
  (f2.F . f1.F)
  (\a, b, m => f2.F' (f1.F a) (f1.F b) (f1.F' a b m))
  (\x => cong (f2.F' (f1.F x) (f1.F x)) (f1.presId x) `trans` f2.presId (f1.F x))
  (\a, b, c, h, j => cong (f2.F' (f1.F _) (f1.F _)) (f1.presComp _ _ _ h j) `trans`
                          f2.presComp _ _ _ (f1.F' _ _ h) (f1.F' _ _ j))

public export
idF : {0 o : Type} -> (0 c : Category o) -> Functor c c
idF c = MkFunctor id (\_, _ => id) (\_ => Refl) (\_, _, _, _, _ => Refl)

