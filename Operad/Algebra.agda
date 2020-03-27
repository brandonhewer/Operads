module Operad.Algebra where

  open import Data.Nat using (ℕ)
  open import Level using (Level; _⊔_; suc)
  open import Operad
  open import Operad.Endo
  open import Operad.Morphism
  
  record Algebra {i : Level} (O : Operad i) (o : Level) : Set (i ⊔ suc o) where
    field
      A : Set o
      ⟦_⟧ : O →ₒ EndoOperad A
