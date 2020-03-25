module Operad.Free where

  open import Data.Container.Indexed using (⟦_⟧)
  open import Data.Fin
  open import Data.Nat using (ℕ)
  open import Data.Product using (_×_; _,_; Σ-syntax)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.W.Indexed
  open import Function using (_∘_)
  open import Level
  open import Operad
  open import Operad.Container
  open import Operad.Nary.Sigma
  open import Relation.Unary

  private
    variable
      n : ℕ
      l₁ l₂ : Level

  open Operad.Operad

  FreeOperad : (K : ℕ -> Set l₁) -> K 1 -> Operad l₁
  Ops (FreeOperad K I) = W (FinContainer K)
  comp' (FreeOperad K I) n op ns ops
    = sup (inj₂ (group n ns) , λ { (inj₁ _) -> op; (inj₂ i) -> proj n ns ops i })
    where
      proj : (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> n ⊗⊤ (λ i → W (FinContainer K) (proj⊤ᵢ i ns)) ->
             (i : Fin n) -> W (FinContainer K) (proj⊤ᵢ i ns)
      proj (ℕ.suc _) _ (op , _) Fin.zero = op
      proj (ℕ.suc n) (_ , ms) (_ , ops) (Fin.suc i) = proj n ms ops i
  id (FreeOperad K I) = sup (inj₁ I , λ ())

  iterₒ : {K : ℕ -> Set l₁} {I : K 1} {O : Operad l₂} -> K ⊆ Ops O -> FreeOperad K I →ₒ O
  iterₒ {K = K} {O = O} ⟪_⟫ = iter (FinContainer K) φ
    where
      φ : ⟦ FinContainer K ⟧ (Ops O) ⊆ Ops O
      φ (inj₁ x , _) = ⟪ x ⟫
      φ (inj₂ (group m ms) , y) = comp' O m (y (inj₁ _)) ms (tabulate (y ∘ inj₂))

  Corolla : (ℕ -> Set l₁) -> ℕ -> Set l₁
  Corolla {l₁} K n = Σ[ G ∈ Grouping l₁ n ] (K (Size G) × (Size G ⊗⊤ λ i -> K (Elem G i)))

  unfoldₒ : {K : ℕ -> Set l₁} {I : K 1} ->
            ({n : ℕ} -> K n -> Corolla K n) ->
            ℕ -> K ⊆ Ops (FreeOperad K I)
  unfoldₒ {K = K} ⟪_⟫ = unfold (λ x -> x) φ
    where
      φ : K ⊆ ⟦ FinContainer K ⟧ K
      φ f = let (g , x , xs) = ⟪ f ⟫ in inj₂ g , λ { (inj₁ _) -> x; (inj₂ i) -> proj⊤ᵢ i xs }

