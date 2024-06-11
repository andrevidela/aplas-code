module Data.Container.Category

import public Data.Category
import public Data.Container
import public Data.Container.Morphism
import public Data.Container.Morphism.Eq

import Proofs.Extensionality

---------------------------------------------------------------------------------------------------
-- Containers form a category                                                                    --
---------------------------------------------------------------------------------------------------

-- Composition respects identity on the right
composeIdRight : (f : a =%> b) -> f ⨾ Morphism.identity = f
composeIdRight (fwd <| bwd) = Refl

-- Composition respects identity on the left
composeIdLeft : (f : a =%> b) -> Morphism.identity ⨾ f = f
composeIdLeft (fwd <| bwd) = Refl

-- Composition is associative
proveAssoc : (f : a =%> b) -> (g : b =%> c) -> (h : c =%> d) ->
             f ⨾ (g ⨾ h) = (f ⨾ g) ⨾ h
proveAssoc (fwd0 <| bwd0) (fwd1 <| bwd1) (fwd2 <| bwd2) = Refl

-- The category of containers with dependent lenses as morphisms
public export
Cont : Category Container
Cont = MkCategory
  (=%>)
  (\_ => Morphism.identity)
  (⨾)
  composeIdRight
  composeIdLeft
  proveAssoc

