module Operad.Nary.Sigma where

  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ; _+_)
  open import Data.Product
  open import Data.Unit
  open import Level
  open import Function using (const)

  private
    variable
      m n : ℕ
      l₁ l₂ : Level
      X : Set l₁
      Y : Set l₂

  π₂ : (Fin (ℕ.suc n) -> X) -> Fin n -> X
  π₂ f i = f (Fin.suc i)
  
  _⊗_ : (n : ℕ) -> (Fin n -> Set l₁) -> Set l₁
  0 ⊗ _ = Level.Lift _ ⊤
  1 ⊗ f = f Fin.zero
  (ℕ.suc (ℕ.suc n)) ⊗ f = f Fin.zero × (ℕ.suc n) ⊗ (π₂ f)

  _⊗⊤_ : (n : ℕ) -> (Fin n -> Set l₁) -> Set l₁
  0 ⊗⊤ _ = Level.Lift _ ⊤
  (ℕ.suc n) ⊗⊤ f = f Fin.zero × n ⊗⊤ (π₂ f)

  _⊛_ : (n : ℕ) -> (X : Set l₁) -> Set l₁
  n ⊛ X = n ⊗ (const X)

  _⊛⊤_ : (n : ℕ) -> (X : Set l₁) -> Set l₁
  n ⊛⊤ X = n ⊗⊤ (const X)

  tabulate : {X : Fin n -> Set l₁} -> ((i : Fin n) -> X i) -> n ⊗⊤ X
  tabulate {0} f = _
  tabulate {ℕ.suc n} f = f Fin.zero , tabulate λ i -> f (Fin.suc i)

  _::_ : X -> (Fin m -> X) -> Fin (ℕ.suc m) -> X
  (X :: _) Fin.zero = X
  (_ :: Xs) (Fin.suc i) = Xs i

  _⊕_ : (Fin m -> X) -> (Fin n -> X) -> Fin (m + n) -> X
  _⊕_ {0} {n = n} _ g i = g i
  _⊕_ {ℕ.suc m} {n = n} f g = f Fin.zero :: (π₂ f ⊕ g)

  proj⊤ᵢ : {F : Fin n -> Set l₁} -> (i : Fin n) -> n ⊗⊤ F -> F i
  proj⊤ᵢ Fin.zero (x , xs) = x
  proj⊤ᵢ (Fin.suc n) (x , xs) = proj⊤ᵢ n xs

  projᵢ : {F : Fin n -> Set l₁} -> (i : Fin n) -> n ⊗ F -> F i
  projᵢ {Data.Fin.1F} Fin.zero x = x
  projᵢ {ℕ.suc (ℕ.suc n)} Fin.zero (x , _) = x
  projᵢ {ℕ.suc (ℕ.suc n)} (Fin.suc i) (_ , xs) = projᵢ i xs

  remove⊤ : (n : ℕ) -> {F : Fin n -> Set l₁} -> n ⊗⊤ F -> n ⊗ F
  remove⊤ 0 x = x
  remove⊤ 1 (x , _) = x
  remove⊤ (ℕ.suc (ℕ.suc n)) (x , xs) = x , remove⊤ (ℕ.suc n) xs

  add⊤ : (n : ℕ) -> {F : Fin n -> Set l₁} -> n ⊗ F -> n ⊗⊤ F
  add⊤ 0 x = x
  add⊤ 1 x = x , _
  add⊤ (ℕ.suc (ℕ.suc n)) (x , xs) = x , add⊤ (ℕ.suc n) xs

  addAll⊤ : (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> n ⊗⊤ (λ i -> proj⊤ᵢ i ns ⊛ X) -> n ⊗⊤ (λ i -> proj⊤ᵢ i ns ⊛⊤ X)
  addAll⊤ 0 _ _ = _
  addAll⊤ (ℕ.suc n) (m , ms) (x , xs) = add⊤ m x , addAll⊤ n ms xs

  ΣFin : (n : ℕ) -> n ⊛⊤ ℕ -> ℕ
  ΣFin 0 _ = 0
  ΣFin (ℕ.suc n) (x , xs) = x + ΣFin n xs

  concat : (m : ℕ) -> (n : ℕ) -> m ⊛⊤ X -> n ⊛⊤ X -> (m + n) ⊛⊤ X
  concat 0 _ _ ys = ys
  concat (ℕ.suc m) n (x , xs) ys = x , concat m n xs ys

  join : (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> n ⊗⊤ (λ i -> proj⊤ᵢ i ns ⊛⊤ X) -> ΣFin n ns ⊛⊤ X
  join 0 _ _ = _
  join (ℕ.suc n) (m , ms) (x , xs) = concat m (ΣFin n ms) x (join n ms xs)

  repeat : {X : Set l₁} -> X -> (n : ℕ) -> n ⊛⊤ X
  repeat _ 0 = _
  repeat x (ℕ.suc n) = x , repeat x n

  repeat-nest : {X : Set l₁} -> X -> (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛⊤ X
  repeat-nest _ 0 _ = _
  repeat-nest x (ℕ.suc n) (m , ms) = repeat x m , repeat-nest x n ms

  
