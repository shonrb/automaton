open import Lang

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _∨_)
open import Data.List.Base using
  (List; []; _∷_; _++_; length; map; concat; foldr; reverse)
open import Data.Sum.Base using
  (_⊎_; inj₁; inj₂)
open import Data.Nat as ℕ using
  (ℕ; zero; suc; _∸_; _+_; _*_; _^_; _<_; _≤_; s≤s; z≤n)
open import Function.Base using
  (_$_; _∘_; _∋_; case_of_; flip; id; const)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; _because_)
open import Data.Unit using
  (⊤; tt)

open FinSet

-- Deterministic Finite Automata
record DFA (Σ : FinSet) : Set₁ where
  constructor DFA[_,_,_,_]
  field
    Q : FinSet
    q₀ : type Q
    ∈F : type Q → Bool
    δ : type Q → type Σ → type Q

compute-dfa' : ∀ {Σ} → (d : DFA Σ) → Σ * → type (DFA.Q d) → Bool
compute-dfa' d [] q = DFA.∈F d q
compute-dfa' d (x ∷ xs) q = compute-dfa' d xs (DFA.δ d q x)

compute-dfa : ∀ {Σ} → (d : DFA Σ) → Σ * → Bool
compute-dfa d w = compute-dfa' d w (DFA.q₀ d)

-- Nondeterministic Finite Automata
data Epsilon : Set where
  epsilon : Epsilon

record NFA (Σ : FinSet) : Set₁ where
  constructor NFA[_,_,_,_]
  field
    Q : FinSet
    q₀ : type Q
    ∈F : type Q → Bool
    δ : type Q → type Σ ⊎ Epsilon → List (type Q)

compute-nfa' : ∀ {Σ} → (n : NFA Σ) → Σ * → List (type (NFA.Q n)) → Bool
compute-nfa' n [] = foldr (_∨_) false ∘ map (NFA.∈F n)
compute-nfa' n (w ∷ ws) qs =
  let next  = map (flip (NFA.δ n) $ (inj₁ w)) qs in
  let empty = map (flip (NFA.δ n) $ (inj₂ epsilon)) qs in
  let all   = concat (next ++ empty) in
  compute-nfa' n ws all

compute-nfa : ∀ {Σ} → (n : NFA Σ) → Σ * → Bool
compute-nfa n x = compute-nfa' n x $ NFA.δ n (NFA.q₀ n) (inj₂ epsilon)

-- All DFAs are NFAs
dfa-to-nfa : ∀ {Σ} → DFA Σ → NFA Σ
NFA.Q (dfa-to-nfa d) = DFA.Q d
NFA.q₀ (dfa-to-nfa d) = DFA.q₀ d
NFA.∈F (dfa-to-nfa d) = DFA.∈F d
NFA.δ (dfa-to-nfa d) q (inj₁ w) = DFA.δ d q w ∷ []
NFA.δ (dfa-to-nfa d) q (inj₂ e) = []

-- Any NFA can be converted to an equivalent DFA
nfa-to-dfa : ∀ {Σ} → NFA Σ → DFA Σ
DFA.Q (nfa-to-dfa n) = {!!}
DFA.q₀ (nfa-to-dfa n) = {!!}
DFA.∈F (nfa-to-dfa n) = {!!}
DFA.δ (nfa-to-dfa n) = {!!}

-- Regular Expressions
emptyᵣ : ∀ {Σ} → NFA Σ
NFA.Q emptyᵣ = Σ-unit
NFA.q₀ emptyᵣ = tt
NFA.∈F emptyᵣ = const $ false
NFA.δ emptyᵣ = const $ const $ []

epsilonᵣ : ∀ {Σ} → NFA Σ
NFA.Q epsilonᵣ = Σ-unit
NFA.q₀ epsilonᵣ = tt
NFA.∈F epsilonᵣ = const true
NFA.δ epsilonᵣ q (inj₁ _) = []
NFA.δ epsilonᵣ q (inj₂ _) = tt ∷ []

singletonᵣ : ∀ {Σ} → type Σ → NFA Σ
NFA.Q  (singletonᵣ x) = Σ-binary
NFA.q₀ (singletonᵣ x) = false
NFA.∈F (singletonᵣ x) = id
NFA.δ (singletonᵣ x) true w = []
NFA.δ (singletonᵣ x) false (inj₂ _) = []
NFA.δ (singletonᵣ {Σ} x) false (inj₁ w) with Σ≟ Σ w x
... | no proof = []
... | yes proof = true ∷ []

*ᵣ : ∀ {Σ} → NFA Σ → NFA Σ
NFA.Q  (*ᵣ NFA[ Q , q₀ , ∈F , δ ]) = Q
NFA.q₀ (*ᵣ NFA[ Q , q₀ , ∈F , δ ]) = q₀
NFA.∈F (*ᵣ NFA[ Q , q₀ , ∈F , δ ]) x = ?
NFA.δ  (*ᵣ NFA[ Q , q₀ , ∈F , δ ]) = {!!}

