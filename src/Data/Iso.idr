module Data.Iso

import Control.Relation
import Control.Order

-- an abstract implementation of Iso for any preorder relation
public export
record GenIso (carrier : Type)
              (mor : Rel carrier)
              (rel : {0 x, y : carrier} -> Rel (mor x y))
              {auto pre : Preorder carrier mor}
              (left, right : carrier) where
  constructor MkGenIso
  to : mor left right
  from : mor right left
  0 toFrom : rel (transitive to from) Relation.reflexive
  0 fromTo : rel (transitive from to) Relation.reflexive

-- a special case of `GenIso` for functions and types with equality
public export
record Iso (left, right : Type) where
  constructor MkIso
  to : left -> right
  from : right -> left
  0 toFrom : (x : right) -> to (from x) = x
  0 fromTo : (x : left) -> from (to x) = x

