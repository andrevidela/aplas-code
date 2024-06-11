module Data.Product

import public Data.Ops
import Data.Vect

%default total
%hide Prelude.(&&)
%hide Prelude.Num.(*)

||| Pairs of types
public export
record (*) (a, b : Type) where
  constructor (&&)
  π1 : a
  π2 : b

%pair (*) π1 π2

public export
elim : (a -> a') -> (b -> b') -> (a' -> b' -> c) -> a * b -> c
elim f g m x = f x.π1 `m` g x.π2

||| Map each element of the pair and combine the results into one using

||| Products have a bifunctor insttance
public export
Bifunctor (*) where
  bimap f1 f2 = elim f1 f2 (&&)


||| From arity 2 to arity 1 with pair
public export
curry : (a * b -> c) -> a -> b -> c
curry f a b = f (a && b)

||| From arity 2 to arity 1 with pair
public export
uncurry : (a -> b -> c) -> a * b -> c
uncurry f x = f x.π1 x.π2

public export
projIdentity : (x : a * b) -> (x.π1 && x.π2) === x
projIdentity (a && b) = Refl
