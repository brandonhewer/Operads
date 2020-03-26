module Operad.Free where

  open import Data.Container.Indexed using (⟦_⟧)
  open import Data.Fin
  open import Data.Nat using (ℕ)
  open import Data.Product using (_×_; _,_; Σ-syntax)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit
  open import Data.W.Indexed
  open import Function using (_∘_)
  open import Level
  open import Operad
  open import Operad.Container
  open import Operad.Morphism using (_→ₒ_)
  open import Operad.Nary.Sigma
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  private
    variable
      n : ℕ
      l₁ l₂ : Level

    FreeId : (K : ℕ -> Set l₁) -> ℕ -> Set l₁
    FreeId K 0 = K 0
    FreeId K 1 = ⊤ ⊎ K 1
    FreeId K (ℕ.suc (ℕ.suc n)) = K (ℕ.suc (ℕ.suc n))

    η : (K : ℕ -> Set l₁) -> K n -> FreeId K n
    η {n = 0} _ x = x
    η {n = 1} K x = inj₂ x
    η {n = ℕ.suc (ℕ.suc n)} _ x = x

    wproj : {K : ℕ -> Set l₁} -> (n : ℕ) -> (ns : n ⊛⊤ ℕ) ->
            n ⊗⊤ (λ i → W (FinContainer (FreeId K)) (proj⊤ᵢ i ns)) ->
            (i : Fin n) -> W (FinContainer (FreeId K)) (proj⊤ᵢ i ns)
    wproj (ℕ.suc _) _ (op , _) Fin.zero = op
    wproj (ℕ.suc n) (_ , ms) (_ , ops) (Fin.suc i) = wproj n ms ops i

    open Operad.Operad

    rep : {K : ℕ -> Set l₁} -> (O : Operad l₂) -> (n : ℕ) -> FreeId K n -> K ⊆ Ops O -> Ops O n
    rep _ 0 x ⟪_⟫ = ⟪ x ⟫
    rep O 1 (inj₁ _) _ = id O
    rep _ 1 (inj₂ x) ⟪_⟫ = ⟪ x ⟫
    rep _ (ℕ.suc (ℕ.suc n)) x ⟪_⟫ = ⟪ x ⟫

    φ : {K : ℕ -> Set l₁} -> (O : Operad l₂) -> K ⊆ Ops O -> ⟦ FinContainer (FreeId K) ⟧ (Ops O) ⊆ Ops O
    φ O ⟪_⟫ {n} (inj₁ x , _) = rep O n x ⟪_⟫ 
    φ O ⟪_⟫ (inj₂ (group m ms) , y) = comp' O m (y (inj₁ _)) ms (tabulate (y ∘ inj₂))

    open _→ₒ_

    tab-map≡ : (K : ℕ -> Set l₁) (O : Operad l₂) (⟪_⟫ : K ⊆ Ops O) (n : ℕ) (ns : n ⊛⊤ ℕ)
               (fs : n ⊗⊤ λ i → W (FinContainer (FreeId K)) (proj⊤ᵢ i ns)) ->
               tabulate (λ i → iter (FinContainer (FreeId K)) (φ O ⟪_⟫) (wproj n ns fs i)) ≡
               map⊤ n (λ z → iter (FinContainer (FreeId K)) (φ O ⟪_⟫)) fs
    tab-map≡ K O ⟪_⟫ 0 _ _ = refl
    tab-map≡ K O ⟪_⟫ (ℕ.suc n) (m , ms) (f , fs)
      = cong (iter (FinContainer (FreeId K)) (φ O ⟪_⟫) f ,_) (tab-map≡ K O ⟪_⟫ n ms fs)

  FreeOperad : (K : ℕ -> Set l₁) -> Operad l₁
  Ops (FreeOperad K) = W (FinContainer (FreeId K))
  comp' (FreeOperad K) n op ns ops
    = sup (inj₂ (group n ns) , λ { (inj₁ _) -> op; (inj₂ i) -> wproj n ns ops i })
  id (FreeOperad K) = sup (inj₁ (inj₁ _) , λ ())

  iterₒ : {K : ℕ -> Set l₁} {O : Operad l₂} -> K ⊆ Ops O -> FreeOperad K →ₒ O
  Oᴹ (iterₒ {K = K} {O = O} ⟪_⟫) = iter (FinContainer (FreeId K)) (φ O ⟪_⟫)
  id≡ (iterₒ _) = refl
  comp≡ (iterₒ {K = K} {O = O} ⟪_⟫) n g ns fs rewrite tab-map≡ K O ⟪_⟫ n ns fs = refl

  Corolla : (ℕ -> Set l₁) -> ℕ -> Set l₁
  Corolla {l₁} K n = Σ[ G ∈ Grouping l₁ n ] (K (Size G) × (Size G ⊗⊤ λ i -> K (Elem G i)))

  unfoldₒ : {K : ℕ -> Set l₁} -> K ⊆ Corolla K -> ℕ -> K ⊆ Ops (FreeOperad K)
  unfoldₒ {K = K} ⟪_⟫ = unfold (λ x -> η K x) ψ
    where
      ψ : K ⊆ ⟦ FinContainer (FreeId K) ⟧ K
      ψ f = let (g , x , xs) = ⟪ f ⟫ in inj₂ g , λ { (inj₁ _) -> x; (inj₂ i) -> proj⊤ᵢ i xs }
