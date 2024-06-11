
module Data.Container.Monad

import Data.Category.Functor

import Data.Container.Category
import Data.Container.Morphism.Eq

%default total

public export
record ContainerMonad (func : Functor Cont Cont) where
  constructor MkContainerMonad
  pure : (a : Container) -> a =%> func.F a
  join : (a : Container) -> func.F (func.F a) =%> func.F a
  0 assoc : forall a.
          let 0 top : func.F (func.F (func.F a)) =%> func.F (func.F a)
              top = join (func.F a)
              0 left : func.F (func.F (func.F a)) =%> func.F (func.F a)
              left = func.F' _ _ (join a)
          in join (func.F a) ⨾ join a `DepLensEq` left ⨾ join a

  0 idl : (a : Container) ->
          pure (func.F a) ⨾ join a `DepLensEq` identity {a = func.F a}
  0 idr : (a : Container) ->
          func.F' _ _ (pure a) ⨾ (join a) `DepLensEq` identity {a = func.F a}

public export
record ContainerComonad (func : Functor Cont Cont) where
  constructor MkContainerComonad
  counit : (a : Container) -> func.F a =%> a
  comult : (a : Container) -> func.F a =%> func.F (func.F a)
  0 assoc : (a : Container) ->
          let 0 top : func.F (func.F a) =%> func.F (func.F (func.F a))
              top = comult (func.F a)
              0 left : func.F (func.F a) =%> func.F (func.F (func.F a))
              left = func.F' _ _ (comult a)
          in comult a ⨾ left `DepLensEq` comult a ⨾ comult (func.F a)
  0 id1 : (a : Container) ->
             comult a ⨾ counit (func.F a) `DepLensEq` identity {a = func.F a}
  0 id2 : (a : Container) ->
             comult a ⨾ func.F' _ _ (counit a) `DepLensEq` identity {a = func.F a}
