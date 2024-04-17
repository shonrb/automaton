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
record DFA : Set₁ where
  constructor DFA[_,_,_,_,_]
  field
    Q : FinSet
    Σ : FinSet
    q₀ : type Q
    ∈F : type Q → Bool
    δ : type Q → type Σ → type Q

compute-dfa' : (d : DFA) → (DFA.Σ d) * → type (DFA.Q d) → Bool
compute-dfa' d [] q = DFA.∈F d q
compute-dfa' d (x ∷ xs) q = compute-dfa' d xs (DFA.δ d q x)

compute-dfa : (d : DFA) → (DFA.Σ d) * → Bool
compute-dfa d w = compute-dfa' d w (DFA.q₀ d)

-- Nondeterministic Finite Automata
data Epsilon : Set where
  epsilon : Epsilon

record NFA : Set₁ where
  constructor NFA[_,_,_,_,_]
  field
    Q : FinSet
    Σ : FinSet
    q₀ : type Q
    ∈F : type Q → Bool
    δ : type Q → type Σ ⊎ Epsilon → List (type Q)

compute-nfa' : (n : NFA) → (NFA.Σ n) * → List (type (NFA.Q n)) → Bool
compute-nfa' n [] = foldr (_∨_) false ∘ map (NFA.∈F n)
compute-nfa' n (w ∷ ws) qs =
  let next  = map (flip (NFA.δ n) $ (inj₁ w)) qs in
  let empty = map (flip (NFA.δ n) $ (inj₂ epsilon)) qs in
  let all   = concat (next ++ empty) in
  compute-nfa' n ws all

compute-nfa : (n : NFA) → (NFA.Σ n) * → Bool
compute-nfa n x = compute-nfa' n x $ NFA.δ n (NFA.q₀ n) (inj₂ epsilon)

-- All DFAs are NFAs
dfa-to-nfa : DFA → NFA
NFA.Q (dfa-to-nfa d) = DFA.Q d
NFA.Σ (dfa-to-nfa d) = DFA.Σ d
NFA.q₀ (dfa-to-nfa d) = DFA.q₀ d
NFA.∈F (dfa-to-nfa d) = DFA.∈F d
NFA.δ (dfa-to-nfa d) q (inj₁ w) = DFA.δ d q w ∷ []
NFA.δ (dfa-to-nfa d) q (inj₂ e) = []

-- Any NFA can be converted to an equivalent DFA
nfa-to-dfa : DFA → NFA
nfa-to-dfa = {!!} -- TODO

-- Regular Expressions
emptyᵣ : {FinSet} → NFA
NFA.Q emptyᵣ = Σ-unit
NFA.Σ (emptyᵣ {Σ}) = Σ
NFA.q₀ emptyᵣ = tt
NFA.∈F emptyᵣ = const $ false
NFA.δ emptyᵣ = const $ const $ []

epsilonᵣ : {FinSet} → NFA
NFA.Q epsilonᵣ = Σ-unit
NFA.Σ (epsilonᵣ {Σ}) = Σ
NFA.q₀ epsilonᵣ = tt
NFA.∈F epsilonᵣ = const true
NFA.δ epsilonᵣ q (inj₁ _) = []
NFA.δ epsilonᵣ q (inj₂ _) = tt ∷ []

singletonᵣ : (Σ : FinSet) → type Σ → NFA
NFA.Q  (singletonᵣ Σ x) = Σ-fin 2
NFA.Σ  (singletonᵣ Σ x) = Σ
NFA.q₀ (singletonᵣ Σ x) = mkFin 0 (s≤s z≤n)
NFA.∈F (singletonᵣ Σ x) q with q ≟ (mkFin 1 (s≤s (s≤s z≤n)))
... | t/f because _ = t/f
NFA.δ (singletonᵣ Σ x) (mkFin .1 (s≤s (s≤s z≤n))) w = []
NFA.δ (singletonᵣ Σ x) (mkFin .0 (s≤s z≤n)) w = {!!}


