module Operad.Endo where

  open import Data.Nat using (ℕ; suc)
  open import Data.Product using (_,_)
  open import Level
  open import Operad
  open import Operad.Nary.Pi

  open Operad.Operad

  EndoOperad : {l₁ : Level} -> (X : Set l₁) -> Operad l₁
  Ops (EndoOperad X) n = n ⊛ X ⇶ X
  comp' (EndoOperad X) 0 x _ _ = x
  comp' (EndoOperad X) 1 g (0 , _) (x , _) = g x
  comp' (EndoOperad X) 1 g (ℕ.suc m , ms) (f , fs) x = comp' (EndoOperad X) 1 g (m , ms) (f x , fs)
  comp' (EndoOperad X) (ℕ.suc (ℕ.suc n)) g (0 , ms) (x , fs) = comp' (EndoOperad X) (ℕ.suc n) (g x) ms fs
  comp' (EndoOperad X) (ℕ.suc (ℕ.suc n)) g (ℕ.suc m , ms) (f , fs) x
    = comp' (EndoOperad X) (ℕ.suc (ℕ.suc n)) g (m , ms) (f x , fs) 
  id (EndoOperad X) x = x
