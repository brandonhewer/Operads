module Operad.Morphism where

  open import Data.Nat using (ℕ)
  open import Level
  open import Operad
  open import Operad.Nary.Sigma
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary using (_⊆_)

  private
    variable
      l₁ l₂ : Level

  open Operad.Operad

  record _→ₒ_ (Op₁ : Operad l₁) (Op₂ : Operad l₂) : Set (l₁ ⊔ l₂) where
    field
      Oᴹ : Ops Op₁ ⊆ Ops Op₂
      id≡ : Oᴹ (id Op₁) ≡ id Op₂
      comp≡ : (n : ℕ) -> (g : Ops Op₁ n) -> (ns : n ⊛⊤ ℕ) -> (fs : n ⊗⊤ λ i -> Ops Op₁ (proj⊤ᵢ i ns)) ->
              Oᴹ (comp' Op₁ n g ns fs) ≡ comp' Op₂ n (Oᴹ g) ns (map⊤ n (λ _ o -> Oᴹ o) fs) 
