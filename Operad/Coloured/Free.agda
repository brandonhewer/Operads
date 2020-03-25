module Operad.Coloured.Free where

  open import Data.Container.Indexed
  open import Data.Fin
  open import Data.Nat using (ℕ)
  open import Data.Product using (_×_; _,_; Σ-syntax)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit
  open import Data.W.Indexed
  open import Level
  open import Operad.Coloured
  open import Operad.Container using (Container⊥)
  open import Operad.Nary.Sigma

  private
    variable
      l₁ l₂ : Level
      n : ℕ

  data Grouping (C : Set l₁) (l₂ : Level) : (n : ℕ) -> n ⊛⊤ C -> C -> Set (l₁ ⊔ l₂) where
    group : (m : ℕ) -> (ms : m ⊛⊤ ℕ) -> (css : m ⊗⊤ λ i -> proj⊤ᵢ i ms ⊛⊤ C) ->
            (rs : m ⊛⊤ C) -> (r : C) -> Grouping C l₂ (ΣFin m ms) (join m ms css) r

  Size : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
         Grouping C l₂ n cs r -> ℕ
  Size (group m _ _ _ _) = m

  Elem : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
         (g : Grouping C l₂ n cs r) -> (i : Fin (Size g)) -> ℕ
  Elem (group _ ms _ _ _) i = proj⊤ᵢ i ms

  Args : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
         (g : Grouping C l₂ n cs r) -> (i : Fin (Size g)) -> Elem g i ⊛⊤ C
  Args (group _ _ cs _ _) i = proj⊤ᵢ i cs

  Rets : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
         (g : Grouping C l₂ n cs r) -> Size g ⊛⊤ C
  Rets (group _ _ _ rs _) = rs

  Res : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
        (g : Grouping C l₂ n cs r) -> (i : Fin (Size g)) -> C
  Res g i = proj⊤ᵢ i (Rets g)

  Ret : {C : Set l₁} {cs : n ⊛⊤ C} {r : C} ->
        (g : Grouping C l₂ n cs r) -> C
  Ret (group _ _ _ _ r) = r

  FinContainer : {C : Set l₁} -> ((n : ℕ) -> n ⊛⊤ C -> C -> Set l₂) ->
                 let Finᶜ = Σ[ n ∈ ℕ ] (n ⊛⊤ C) × C in Container Finᶜ Finᶜ (l₁ ⊔ l₂) 0ℓ
  FinContainer {l₁} {l₂} {C = C} K
    = Container⊥ (λ {(n , cs , c) -> Grouping C l₂ n cs c}) (λ {(n , cs , c) -> K n cs c})
        (λ g -> ⊤ ⊎ Fin (Size g))
        (λ g -> λ { (inj₁ _) -> Size g , Rets g , Ret g; (inj₂ i) -> Elem g i , Args g i , Res g i })

  open Operad.Coloured.ColouredOperad

  FreeOperad : {C : Set l₁} -> (K : (n : ℕ) -> n ⊛⊤ C -> C -> Set l₂) ->
                (I : (c : C) -> K 1 (c , _) c) -> ColouredOperad (l₁ ⊔ l₂) C
  Ops' (FreeOperad K I) n as r = W (FinContainer K) (n , as , r)
  comp' (FreeOperad {C = C} K I) n cs r op ns css ops
    = sup (inj₂ (group n ns css cs r) , λ { (inj₁ _) -> op; (inj₂ i) -> proj n ns cs css ops i })
    where
      proj : (n : ℕ) -> (ns : n ⊛⊤ ℕ) -> (cs : n ⊛⊤ C) -> (css : n ⊗⊤ λ i -> proj⊤ᵢ i ns ⊛⊤ C) ->
             n ⊗⊤ (λ i → W (FinContainer K) (proj⊤ᵢ i ns , proj⊤ᵢ i css , proj⊤ᵢ i cs)) ->
             (i : Fin n) -> W (FinContainer K) (proj⊤ᵢ i ns , proj⊤ᵢ i css , proj⊤ᵢ i cs)
      proj (ℕ.suc _) _ _ _ (op , _) Fin.zero = op
      proj (ℕ.suc n) (_ , ms) (_ , cs) (_ , css) (_ , ops) (Fin.suc i) = proj n ms cs css ops i
  id (FreeOperad K I) c = sup (inj₁ (I c) , λ ())
