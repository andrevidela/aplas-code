module Data.Category

import public Data.Category.Ops

private infixr 1 ~:>  -- Explicit morphism
private infixl 5 |:>  -- Explicit composition

public export
record Category (o : Type) where
  constructor MkCategory
  0 (~:>) : o -> o -> Type
  id : (v : o) -> v ~:> v
  (|:>) : {0 a, b, c : o} -> (a ~:> b) -> (b ~:> c) -> (a ~:> c)
  0 idLeft : {a, b : o} -> (f : a ~:> b) -> f |:> id b = f
  0 idRight : {a, b : o} -> (f : a ~:> b) -> id a |:> f = f
  0 compAssoc : {a, b, c, d : o} ->
                (f : a ~:> b) ->
                (g : b ~:> c) ->
                (h : c ~:> d) ->
                f |:> (g |:> h) = (f |:> g) |:> h

-- An operator for morphisms without passing the category in argument
public export
0 (~>) : (cat : Category o) => o -> o -> Type
(~>) = Category.(~:>) cat

-- An operator for sequential composition without passing in the category in argument
public export
(|>) : (cat : Category o) => {0 a, b, c : o} ->
       a ~> b -> b ~> c -> a ~> c
(|>) = Category.(|:>) cat

-- The opposite category
public export
(.op) : Category o -> Category o
(.op) cat = MkCategory
    (\x, y => y ~> x)
    (cat.id)
    (\f, g => (|:>) cat g f )
    (cat.idRight)
    (cat.idLeft)
    (\f, g, h => sym (cat.compAssoc h g f))

public export
Idris : Category Type
Idris = MkCategory
  (\a, b => a -> b)
  (\_ => id)
  (\f, g => g . f)
  (\_ => Refl)
  (\_ => Refl)
  (\_, _, _ => Refl)
