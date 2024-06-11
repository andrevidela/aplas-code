module Data.Coproduct

import public Data.Ops
import Proofs.Extensionality

%default total

||| co-products
public export
data (+) : Type -> Type -> Type where
  ||| Left choice
  (<+) : a -> a + b
  ||| Right choice
  (+>) : b -> a + b

||| Eliminator for co-products
public export
choice : (a -> c) -> (b -> c) -> a + b -> c
choice f g (<+ x) = f x
choice f g (+> x) = g x

public export
dia : a + a -> a
dia (<+ x) = x
dia (+> x) = x


||| Co-product is a bifunctor
export
Bifunctor (+) where
  bimap f g (<+ x) = <+ (f x)
  bimap f g (+> x) = +> (g x)

-- Proofs about bifunctoriality

public export
0 bifunctorId' : {0 a, b : Type} ->
                 (x : a + b) ->
                Prelude.Interfaces.bimap {f = (+)} (Prelude.id {a}) (Prelude.id {a=b}) x
                === x
bifunctorId' (<+ x) = Refl
bifunctorId' (+> x) = Refl

public export 0
bimapCompose : (x : a + b) ->
               Prelude.Interfaces.bimap {f = (+)} (g . f) (k . l) x
           === Prelude.Interfaces.bimap {f = (+)} g k (Prelude.Interfaces.bimap f l x)
bimapCompose (<+ x) = Refl
bimapCompose (+> x) = Refl

public export
bimapChoice : {0 a, b, a', b' : Type} ->
              {0 f : a -> Type} -> {0 g : b -> Type} ->
              {0 f' : a' -> Type} -> {0 g' : b' -> Type} ->
              (fwd1 : a -> a') ->
              (bwd1 : (x : a) -> f' (fwd1 x) -> f x) ->
              (fwd2 : b -> b') ->
              (bwd2 : (x : b) -> g' (fwd2 x) -> g x) ->
              (x : a + b) ->
              choice f' g' (bimap fwd1 fwd2 x) ->
              choice f g x
bimapChoice fwd1 bwd1 fwd2 bwd2 (<+ x) y = bwd1 x y
bimapChoice fwd1 bwd1 fwd2 bwd2 (+> x) y = bwd2 x y

export
bimapChoiceId : {0 a, b : Type} -> {0 f : a -> Type} -> {0 g : b -> Type} ->
                (x : a + b) ->
                (y : choice f g (bimap Basics.id Basics.id x)) ->
                bimapChoice {f' = f, g' = g} Basics.id (\_ => Basics.id) Basics.id (\_ => Basics.id) x y
                === replace {p = choice f g} (bifunctorId' x) y
bimapChoiceId (<+ x) y = Refl
bimapChoiceId (+> x) y = Refl

export
bimapChoiceComp : forall a1, a2, a3, b1, b2, b3.
   {0 f1 : a1 -> Type} -> {0 g1 : b1 -> Type} ->
   {0 f2 : a2 -> Type} -> {0 g2 : b2 -> Type} ->
   {0 f3 : a3 -> Type} -> {0 g3 : b3 -> Type} ->
   (fwda12 : a1 -> a2) ->
   (bwda12 : (x : a1) -> f2 (fwda12 x) -> f1 x) ->
   (fwdb12 : b1 -> b2) ->
   (bwdb12 : (x : b1) -> g2 (fwdb12 x) -> g1 x) ->
   (fwda23 : a2 -> a3) ->
   (bwda23 : (x : a2) -> f3 (fwda23 x) -> f2 x) ->
   (fwdb23 : b2 -> b3) ->
   (bwdb23 : (x : b2) -> g3 (fwdb23 x) -> g2 x) ->
   (vx : a1 + b1) ->
   (vy : Coproduct.choice f3 g3 (bimap (\x => fwda23 (fwda12 x)) (\x => fwdb23 (fwdb12 x)) vx)) ->
   bimapChoice {f' = f3, g' = g3}
       (\x => fwda23 (fwda12 x))
       (\z, x => bwda12 z (bwda23 (fwda12 z) x))
       (\x => fwdb23 (fwdb12 x))
       (\z, x => bwdb12 z (bwdb23 (fwdb12 z) x))
       vx vy
       === let
           ppp : choice f3 g3 (bimap fwda23 fwdb23 (bimap fwda12 fwdb12 vx))
           ppp = (replace {p = choice f3 g3} (bimapCompose vx) vy)
           choice1 : choice f2 g2 (bimap fwda12 fwdb12 vx)
           choice1 = bimapChoice {f = f2, f' = f3, g = g2, g' = g3} fwda23 bwda23 fwdb23 bwdb23 (bimap fwda12 fwdb12 vx) ppp
           choice2 : choice f1 g1 vx
           choice2 = bimapChoice {f = f1, f' = f2, g = g1, g' = g2} fwda12 bwda12 fwdb12 bwdb12 vx choice1
         in choice2
bimapChoiceComp fwda12 bwda12 fwdb12 bwdb12 fwda23 bwda23 fwdb23 bwdb23 (<+ x) vy = Refl
bimapChoiceComp fwda12 bwda12 fwdb12 bwdb12 fwda23 bwda23 fwdb23 bwdb23 (+> x) vy = Refl


