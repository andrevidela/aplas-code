module Data.Category.NaturalTransformation

import public Data.Category.Functor

%unbound_implicits off

public export
record (==>>) {0 cObj, dObj : Type} {0 c : Category cObj} {0 d : Category dObj}
              (f, g : Functor c d) where
  constructor MkNT
  comp : (v : cObj) -> (f.F v) ~> (g.F v)

  --                η x
  --   x      F x ───────> G x
  --   │       │             │
  --  m│   F m │             │ G m
  --   │       │             │
  --   v       v             v
  --   y      F y ───────> G y
  --                η y
  0 commutes : (0 x, y : cObj) -> (m : x ~> y) ->
      let 0 top : f.F x ~> g.F x
          top = comp x

          0 bot : f.F y ~> g.F y
          bot = comp y

          0 left : f.F x ~> f.F y
          left = f.F' _ _ m

          0 right : g.F x ~> g.F y
          right = g.F' _ _ m

          0 comp1 : f.F x ~> g.F y
          comp1 = top |> right

          0 comp2 : f.F x ~> g.F y
          comp2 = left |> bot

      in comp1 === comp2

