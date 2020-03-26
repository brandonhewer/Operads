module Operad.Coloured.Colour where

  open import Data.Nat
  open import Data.Product using (_,_)
  open import Data.Unit
  open import Level
  open import Operad
  open import Operad.Coloured
  open import Operad.Nary.Sigma
  open import Relation.Binary.PropositionalEquality

  private
    variable
      l₁ l₂ : Level

  open ColouredOperad
  open Operad.Operad

  colour : Operad l₁ -> ColouredOperad l₁ ⊤
  Ops' (colour O) n _ _ = Ops O n
  comp' (colour O) n _ _ g ns _ fs = comp' O n g ns fs
  id (colour O) _ = id O

  join-repeat : {X : Set l₁} -> (x : X) -> (n : ℕ) -> (ns : n ⊛⊤ ℕ) ->
                join n ns (repeat-nest x n ns) ≡ repeat x (ΣFin n ns)
  join-repeat _ 0 _ = refl
  join-repeat _ 1 (m , _) = refl
  join-repeat x (ℕ.suc (ℕ.suc n)) (0 , ms) = join-repeat x (ℕ.suc n) ms
  join-repeat x (ℕ.suc (ℕ.suc n)) (ℕ.suc m , ms) = cong (x ,_) (join-repeat x (ℕ.suc (ℕ.suc n)) (m , ms))

  discolour : ColouredOperad l₁ ⊤ -> Operad l₁
  Ops (discolour O) n = Ops' O n (repeat _ n) _
  comp' (discolour O) n g ns fs =
    subst (λ ⊤s -> Ops' O (ΣFin n ns) ⊤s _) (join-repeat tt n ns)
          (comp' O n (repeat _ n) _ g ns (repeat-nest _ n ns) (nest-rewrite O _ n ns fs))
    where
      nest-rewrite : {X : Set l₁} -> (O : ColouredOperad l₂ X) ->
                     (x : X) -> (n : ℕ) -> (ns : n ⊛⊤ ℕ) ->
                     n ⊗⊤ (λ i -> Ops' O (proj⊤ᵢ i ns) (repeat x (proj⊤ᵢ i ns)) x) ->
                     n ⊗⊤ λ i -> Ops' O (proj⊤ᵢ i ns) (proj⊤ᵢ i (repeat-nest x n ns)) (proj⊤ᵢ i (repeat x n))
      nest-rewrite O _ 0 _ _ = _
      nest-rewrite O x (ℕ.suc n) (m , ms) (f , fs) = f , nest-rewrite O x n ms fs
  id (discolour O) = id O _
