module Operad.Nary.Pi where

  open import Data.Fin
  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_)
  open import Function using (const)
  open import Level
  open import Operad.Nary.Sigma

  private
    variable
      l₁ l₂ : Level
      X : Set l₁
      Y : Set l₂

  apply : (n : ℕ) -> {F : Fin (ℕ.suc n) -> Set l₁} -> (ℕ.suc n ⊗⊤ F -> Y) -> F Fin.zero -> n ⊗⊤ π₂ F -> Y
  apply 0 f x _ = f (x , _)
  apply (ℕ.suc n) f x xs = f (x , xs)

  ΠFin : (n : ℕ) -> (F : Fin n -> Set l₁) -> (n ⊗⊤ F -> Set l₂) -> Set (l₁ ⊔ l₂)
  ΠFin {l₁} 0 _ rf = Lift l₁ (rf _)
  ΠFin {l₁} 1 as rf = (x : as Fin.zero) -> rf (x , _)
  ΠFin (ℕ.suc (ℕ.suc n)) as rf = (x : as Fin.zero) -> ΠFin (ℕ.suc n) (π₂ as) (apply (ℕ.suc n) {as} rf x)

  syntax ΠFin n as (λ xs -> r) = Π[ xs ∈ n ⊗ as ] r

  _⊗_⇶_ : (n : ℕ) -> (Fin n -> Set l₁) -> Set l₁ -> Set l₁
  _⊗_⇶_ {l₁} 0 _ r = r
  ℕ.suc n ⊗ as ⇶ r = as Fin.zero -> n ⊗ π₂ as ⇶ r 

  _⊛_⇶_ : (n : ℕ) -> Set l₁ -> Set l₁ -> Set l₁
  n ⊛ a ⇶ r = n ⊗ const a ⇶ r

  curry : (n : ℕ) -> {as : Fin n -> Set l₁} {R : n ⊗⊤ as -> Set l₂} -> ((xs : n ⊗⊤ as) -> R xs) -> ΠFin n as R 
  curry 0 f = record { lower = f _ }
  curry 1 f x = f (x , _)
  curry (ℕ.suc (ℕ.suc n)) f x = curry (ℕ.suc n) λ xs -> f (x , xs)

  curry' : (n : ℕ) -> {as : Fin n -> Set l₁} -> (n ⊗⊤ as -> X) -> n ⊗ as ⇶ X
  curry' 0 f = f _
  curry' 1 f x = f (x , _)
  curry' (ℕ.suc (ℕ.suc n)) {as} f x = curry' (ℕ.suc n) {π₂ as} λ xs -> f (x , xs)

  uncurry : (n : ℕ) -> {as : Fin n -> Set l₁} {R : n ⊗⊤ as -> Set l₂} -> ΠFin n as R -> (xs : n ⊗⊤ as) -> R xs
  uncurry 0 x _ = lower x
  uncurry 1 f (x , _) = f x
  uncurry (ℕ.suc (ℕ.suc n)) f (x , xs) = uncurry (ℕ.suc n) (f x) xs
