module Data.Container.Maybe

import Data.Container.Morphism

public export
maybeMap : (a -> b) -> Maybe a -> Maybe b
maybeMap f (Just x) = Just (f x)
maybeMap f Nothing = Nothing

public export
maybeJoin : Maybe (Maybe x) -> Maybe x
maybeJoin (Just (Just v)) = Just v
maybeJoin _ = Nothing

public export
data All : (x -> Type) -> Maybe x -> Type where
  Nah : All pred Nothing
  Aye : {v : x} -> pred v -> All pred (Just v)

public export
obtain : All p (Just a) -> p a
obtain (Aye x) = x

public export
MaybeAllIdris : Container -> Container
MaybeAllIdris c = (!>) (Maybe c.req) (All c.res)

public export
maybeAllPure : (x : Container) -> x =%> MaybeAllIdris x
maybeAllPure _ = Just <| \x, y => obtain y

public export
maybeAllJoinBwd : (x : Maybe (Maybe a)) -> All f (Maybe.maybeJoin x) -> All (All f) x
maybeAllJoinBwd (Just (Just v)) (Aye y) = Aye (Aye y)
maybeAllJoinBwd (Just Nothing) b = Aye Nah
maybeAllJoinBwd Nothing b = Nah

public export
maybeAllJoin : (x : Container) -> MaybeAllIdris (MaybeAllIdris x) =%> MaybeAllIdris x
maybeAllJoin _ =  maybeJoin <| maybeAllJoinBwd

public export
bwdMaybeAllF: {0 x, y : Container} -> {mor : x =%> y} -> (v : Maybe x.req) ->
              All y.res (maybeMap mor.fwd v) -> All x.res v
bwdMaybeAllF Nothing Nah = Nah
bwdMaybeAllF (Just v) (Aye z) = Aye (mor.bwd v z)

public export
MaybeAllIdrisFunctor : a =%> b -> MaybeAllIdris a =%> MaybeAllIdris b
MaybeAllIdrisFunctor x = maybeMap x.fwd <| bwdMaybeAllF
