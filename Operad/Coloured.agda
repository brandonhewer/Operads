module Operad.Coloured where

  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_)
  open import Function using (const)
  open import Level
  open import Operad.Nary.Sigma
  open import Operad.Nary.Pi

  private
    variable
      l₁ : Level

  record ColouredOperad (l : Level) (C : Set l₁) : Set (suc l ⊔ l₁) where
    field
      Ops' : (n : ℕ) -> (n ⊛⊤ C) -> C -> Set l
      comp' : (n : ℕ) ->
              (cs : n ⊛⊤ C) ->
              (R : C) ->
              Ops' n cs R ->
              (ns : n ⊛⊤ ℕ) ->
              (css : n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛⊤ C) ->
              n ⊗⊤ (λ i -> Ops' (proj⊤ᵢ i ns) (proj⊤ᵢ i css) (proj⊤ᵢ i cs)) ->
              Ops' (ΣFin n ns) (join n ns css) R
      id : (c : C) -> Ops' 1 (c , _) c

    Opsᶜ : (n : ℕ) -> Π[ _ ∈ n ⊗ const C ] (C -> Set l)
    Opsᶜ n = curry n (Ops' n)

    compᶜ : (n : ℕ) -> Π[ cs ∈ n ⊗ const C ] (
              (R : C) -> Ops' n cs R -> Π[ ns ∈ n ⊗ const ℕ ] (
                Π[ css ∈ n ⊗ (λ i -> proj⊤ᵢ i ns ⊛ C) ] (
                  let css' = addAll⊤ n ns css in
                  n ⊗ (λ i -> Ops' (proj⊤ᵢ i ns) (proj⊤ᵢ i css') (proj⊤ᵢ i cs)) ⇶
                               Ops' (ΣFin n ns) (join n ns css') R
                )
              )
            )
    compᶜ n = curry n λ cs R op -> curry n λ ns -> curry n (comp'' n cs R op ns)
      where
        comp'' : (n : ℕ) -> (cs : n ⊛⊤ C) -> (R : C) -> Ops' n cs R ->
                 (ns : n ⊛⊤ ℕ) -> (css : n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛ C) ->
                 let css' = addAll⊤ n ns css in
                   n ⊗ (λ i -> Ops' (proj⊤ᵢ i ns) (proj⊤ᵢ i css') (proj⊤ᵢ i cs)) ⇶
                   Ops' (ΣFin n ns) (join n ns css') R
        comp'' n cs R op ns css = curry' n (comp' n cs R op ns (addAll⊤ n ns css))
