module Operad.Nary.Sigma.Properties where

  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_)
  open import Function using (const)
  open import Level using (Level)
  open import Operad.Nary.Sigma
  open import Relation.Binary.PropositionalEquality

  private
    variable
      l₁ l₂ l₃ : Level

  join-map≡ : (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> {X : Set l₁} -> (xss : n ⊗⊤ (λ i → proj⊤ᵢ i ns ⊛⊤ X)) ->
              {Y : Set l₂} -> (f : X -> Y) ->
              join n ns (map⊤ n (λ i → map⊤ (proj⊤ᵢ i ns) (const f)) xss) ≡
              map⊤ (ΣFin n ns) (const f) (join n ns xss)
  join-map≡ 0 _ _ _ = refl
  join-map≡ 1 (m, , _) (xs , _) f = refl
  join-map≡ (ℕ.suc (ℕ.suc n)) (0 , ms) (xs , xss) f = join-map≡ (ℕ.suc n) ms xss f
  join-map≡ (ℕ.suc (ℕ.suc n)) (ℕ.suc m , ms) ((x , xs) , xss) f
    = cong (f x ,_) (join-map≡ (ℕ.suc (ℕ.suc n)) (m , ms) (xs , xss) f)

  tab-map≡ : (n : ℕ) -> {I : Set l₁} -> (is : n ⊛⊤ I) ->
             {A : I -> Set l₂} -> (xs : n ⊗⊤ λ i -> A (proj⊤ᵢ i is)) ->
             {B : I -> Set l₃} -> (f : (i : Fin n) -> A (proj⊤ᵢ i is) -> B (proj⊤ᵢ i is)) ->
             tabulate (λ i -> f i (proj⊤ᵢ i xs)) ≡ map⊤ n f xs
  tab-map≡ 0 _ _ _ = refl
  tab-map≡ (ℕ.suc n) (_ , is) {A} (x , xs) {B} f
    = cong (f Fin.zero x ,_) (tab-map≡ n is {A} xs {B} λ i -> f (Fin.suc i))
