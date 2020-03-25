module Operad.Container where

  open import Data.Container.Indexed
  open import Data.Empty
  open import Data.Fin
  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit
  open import Data.W.Indexed
  open import Level
  open import Operad.Nary.Sigma
  open import Relation.Unary

  private
    variable
      l₁ l₂ l₃ l₄ l₅ : Level
      n : ℕ

  data Grouping (l : Level) : ℕ -> Set l where
    group : (m : ℕ) -> (ms : m ⊛⊤ ℕ) -> Grouping l (ΣFin m ms)

  Size : Grouping l₁ n -> ℕ
  Size (group n _) = n

  Elem : (g : Grouping l₁ n) -> Fin (Size g) -> ℕ
  Elem (group _ ns) i = proj⊤ᵢ i ns

  Container⊥ : {I : Set l₁} {O : Set l₂} ->
               (C : O -> Set l₃) ->
               (C⊥ : O -> Set l₄) ->
               (R : {o : O} -> C o -> Set l₅) ->
               (N : {o : O} -> (c : C o) -> R c -> I) ->
               Container I O (l₃ ⊔ l₄) l₅
  Command (Container⊥ C C⊥ R N) x = C⊥ x ⊎ C x
  Response (Container⊥ C C⊥ R N) (inj₁ _) = Lift _ ⊥
  Response (Container⊥ C C⊥ R N) (inj₂ c) = R c
  next (Container⊥ C C⊥ R N) (inj₂ c) r = N c r

  FinContainer : (ℕ -> Set l₁) -> Container ℕ ℕ l₁ 0ℓ
  FinContainer {l} K
    = Container⊥ (Grouping l) K
        (λ g -> ⊤ ⊎ Fin (Size g))
        (λ g -> λ { (inj₁ _) -> Size g; (inj₂ i) -> Elem g i })

  unfold : {O : Set l₁} ->
           {C : O -> Set l₂} ->
           {C⊥ : O -> Set l₂} ->
           {R : {o : O} -> C o -> Set l₃} ->
           {N : {o : O} -> (c : C o) -> R c -> O} ->
           {X : Pred O l₄} ->
           let C = Container⊥ C C⊥ R N in
           X ⊆ C⊥ -> X ⊆ ⟦ C ⟧ X -> ℕ -> X ⊆ W C
  unfold ε φ 0 x = sup (inj₁ (ε x) , λ ())
  unfold {C = C} {C⊥ = C⊥} {R = R} {N = N} {X = X} ε φ (ℕ.suc n) x = sup (ψ (φ x))
    where
      ψ : let C = Container⊥ C C⊥ R N in ⟦ C ⟧ X ⊆ ⟦ C ⟧ (W C)
      ψ (x , y) = x , λ r → unfold ε φ n (y r)
