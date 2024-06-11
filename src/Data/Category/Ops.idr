module Data.Category.Ops

export infixr 1 ~>   -- Morphisms
export infixl 5 |>   -- Composition
export infixl 5 #>   -- Action
export infix 3 <>

export infixr 4 >>-
export infixr 4 -<<

export infix 1 =~= -- Isomorphisms

export infixr 7 -*> -- Functor
export infixr 1 ==>> -- Natural Transformations
export infixr 2 *> -- Natural Transformations

-- container things
export infixl 6 ○
export infixl 7 ⊗
export infixl 6 ×
export infix 5 :-
export typebind infixr 0 !>
export infixl 0 !!> -- natural transformation composition

export infixr 1 =%>
export infix 5 <| -- container morphisms
export infixl 1 ⨾ -- composition
