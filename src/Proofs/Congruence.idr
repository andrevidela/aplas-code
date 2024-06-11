module Proofs.Congruence

public export
cong2Dep :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  (f : ((x : t1) -> t2 x -> t3)) ->
  {0 a, b : t1} ->
  {0 c : t2 a} ->
  {0 d : t2 b} ->
  (p : a === b) ->
  c === (rewrite p in d) ->
  f a c = f b d
cong2Dep f Refl Refl = Refl

public export
app : (f : a -> b) -> (g : a -> b) -> f === g -> (x : a) -> f x === g x
app f f Refl x = Refl

