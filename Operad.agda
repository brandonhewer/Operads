module Operad where

  open import Data.Nat using (ℕ; _+_)
  open import Data.Product using (_,_)
  open import Function using (const)
  open import Level
  open import Operad.Nary.Sigma
  open import Operad.Nary.Pi
 
  record Operad (l : Level) : Set (suc l) where
    field
      Ops : (n : ℕ) -> Set l
      comp' : (n : ℕ) -> Ops n -> (ns : n ⊛⊤ ℕ) -> n ⊗⊤ (λ i -> Ops (proj⊤ᵢ i ns)) -> Ops (ΣFin n ns)
      id : Ops 1

    comp : (n : ℕ) -> Ops n ->
           Π[ ns ∈ n ⊗ const ℕ ]
           (n ⊗ (λ i -> Ops (proj⊤ᵢ i ns)) ⇶
           Ops (ΣFin n ns))
    comp n op = curry n λ ns -> curry' n λ ops -> comp' n op ns ops

  _→ₒ_ : {l₁ l₂ : Level} -> (Op₁ : Operad l₁) -> (Op₂ : Operad l₂) -> Set (l₁ ⊔ l₂)
  Op₁ →ₒ Op₂ = ∀ {n} -> Operad.Ops Op₁ n -> Operad.Ops Op₂ n
