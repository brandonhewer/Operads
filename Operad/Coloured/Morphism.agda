module Operad.Coloured.Morphism where

  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties
  open import Data.Product using (_,_)
  open import Function using (const)
  open import Level using (Level; _⊔_)
  open import Operad.Coloured
  open import Operad.Nary.Sigma
  open import Operad.Nary.Sigma.Properties
  open import Relation.Binary.PropositionalEquality

  private
    variable
      l₁ l₂ l₃ l₄ : Level

    open ColouredOperad

    map-ops : {C₁ : Set l₁} {C₂ : Set l₂} ->
              (O₁ : ColouredOperad l₃ C₁) (O₂ : ColouredOperad l₄ C₂) ->
              (n : ℕ) -> (ns : n ⊛⊤ ℕ) ->
              (cs : n ⊛⊤ C₁) -> (css : n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛⊤ C₁) ->
              (fs : n ⊗⊤ λ i -> Ops' O₁ (proj⊤ᵢ i ns) (proj⊤ᵢ i css) (proj⊤ᵢ i cs)) ->
              (Cᴹ : C₁ -> C₂) ->
              (Oᴹ : ∀ {n cs r} -> Ops' O₁ n cs r -> Ops' O₂ n (map⊤ n (const Cᴹ) cs) (Cᴹ r)) ->
              n ⊗⊤ (λ i → Ops' O₂ (proj⊤ᵢ i ns) (proj⊤ᵢ i (map⊤ n (λ j → map⊤ (proj⊤ᵢ j ns) (const Cᴹ)) css))
                    (proj⊤ᵢ i (map⊤ n (const Cᴹ) cs)))
    map-ops _ _ 0 _ _ _ _ _ _ = _
    map-ops O₁ O₂ (ℕ.suc n) (m , ms) (_ , cs) (_ , css) (f , fs) Cᴹ Oᴹ
      = Oᴹ f , map-ops O₁ O₂ n ms cs css fs Cᴹ Oᴹ

  record _→ₒ_ {C₁ : Set l₁} {C₂ : Set l₂} (O₁ : ColouredOperad l₃ C₁) (O₂ : ColouredOperad l₄ C₂)
              : Set (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
    field
      Cᴹ : C₁ -> C₂
      Oᴹ : ∀ {n cs r} -> Ops' O₁ n cs r -> Ops' O₂ n (map⊤ n (const Cᴹ) cs) (Cᴹ r)
      id≡ : (c : C₁) -> Oᴹ (id O₁ c) ≡ id O₂ (Cᴹ c)
      comp≡ : (n : ℕ) -> (cs : n ⊛⊤ C₁) -> (r : C₁) -> (g : Ops' O₁ n cs r) ->
              (ns : n ⊛⊤ ℕ) -> (css : n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛⊤ C₁) ->
              (fs : n ⊗⊤ λ i -> Ops' O₁ (proj⊤ᵢ i ns) (proj⊤ᵢ i css) (proj⊤ᵢ i cs)) ->
              Oᴹ (comp' O₁ n cs r g ns css fs) ≡
              subst (λ x -> Ops' O₂ (ΣFin n ns) x (Cᴹ r)) (join-map≡ n ns css Cᴹ)
                (comp' O₂ n (map⊤ n (const Cᴹ) cs) (Cᴹ r) (Oᴹ g) ns
                            (map⊤ n (λ i x -> map⊤ (proj⊤ᵢ i ns) (const Cᴹ) x) css)
                            (map-ops O₁ O₂ n ns cs css fs Cᴹ Oᴹ))
