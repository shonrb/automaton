{-# OPTIONS --allow-unsolved-metas #-}

open import FinSet
open import Reg using (Epsilon)

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _∨_)
open import Data.List.Base using
  (List; []; _∷_; _++_; length; map; concat; foldr; reverse)
open import Data.Sum.Base using
  (_⊎_; inj₁; inj₂)
open import Data.Product using
  (_×_; _,′_)

open FinSet.FinSet

-- Pushdown automata

record PDA (Σ : FinSet) : Set₁ where
  constructor PDA[_,_,_,_,_]
  field
    Q : FinSet
    Γ : FinSet
    q₀ : type Q
    ∈F : type Q → Bool
    δ : type Q
      → type Σ ⊎ Epsilon
      → type Γ ⊎ Epsilon
      → List (type Q × (type Γ ⊎ Epsilon))

compute-pda : ∀ {Σ} → PDA Σ → Σ * → Bool
compute-pda = {!!} where
  compute-pda-inner : ∀ {Σ} → (n : PDA Σ) → Σ *
                    → List (type (PDA.Q n)) → List (type (PDA.Γ n)) → Bool
  compute-pda-inner n input states stack = {!!}

