module Data.Category.Monad

import Data.Category
import Data.Category.NaturalTransformation
import Data.Category.Functor

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.Monad

public export
record Monad (c : Category o) where
  constructor MkMonad
  endo : Functor c c
  η : idF c ==>> endo
  μ : (endo *> endo) ==>> endo

  --             F join
  -- F (F (F x)) ───────> F (F x)
  --    │                   │
  --    │ join (F x)        │ join
  --    │                   │
  --    V                   V
  --  F (F x)  ──────────> F x
  --              join
  0 square : (x : o) -> let
      top : endo.F (endo.F (endo.F x)) ~> endo.F (endo.F x)
      top = endo.F' _ _ (comp μ x)
      bot, right : endo.F (endo.F x) ~> endo.F x
      right = comp μ x
      bot = comp μ x
      left : endo.F (endo.F (endo.F x)) ~> endo.F (endo.F x)
      left = comp μ (endo.F x)
      0 arm2, arm1 : endo.F (endo.F (endo.F x)) ~> endo.F x
      arm1 = (top |> right) {cat = c}
      arm2 = left |> bot
      in arm1 === arm2

  -- identity triangles
  --         η (F x)
  --      F x ──> F (F x)
  --       │  ╲     │
  --       │   ╲    │
  --   F η │    =   │ μ
  --       │     ╲  │
  --       V      ╲ V
  --    F (F x) ──> F x
  --            μ
  0 identityLeft : (x : o) -> let
      0 compose : endo.F x ~> endo.F x
      compose = (comp η (endo.F x) |> comp μ x) {cat = c}
      0 straight : endo.F x ~> endo.F x
      straight = c.id (endo.F x)
      in compose === straight

  0 identityRight : (x : o) -> let
      0 compose : endo.F x ~> endo.F x
      compose = (endo.F' _ _ (comp η x) |> comp μ x) {cat = c}
      0 straight : endo.F x ~> endo.F x
      straight = c.id (endo.F x)
      in compose === straight

