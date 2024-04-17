open import Data.Nat as ℕ using
  (ℕ; zero; suc; _∸_; _+_; _*_; _<_; _≤_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; subst; module ≡-Reasoning)
open import Data.Bool.Base using
  (Bool; true; false; _∧_; _∨_)
open import Function.Base using
  (_$_; _∘_; _∋_; case_of_; flip; id; const)
open import Data.List.Base using
  (List; []; _∷_; _++_; reverse)
open import Relation.Nullary.Decidable using
  (Dec; yes; no)
open import Data.Unit using
  (⊤; tt)

import Data.Nat.Properties as ℕₚ

-- Finite natural numbers
record Fin (n : ℕ) : Set where
  constructor mkFin
  field
    value : ℕ
    bounded : value < n

-- Decidable equality of finite numbers
fin-val-≡ : ∀ {n} {k l : Fin n} → Fin.value k ≡ Fin.value l → k ≡ l
fin-val-≡ {_} {mkFin v b₁} {mkFin .v b₂} refl
  rewrite ℕₚ.<-irrelevant b₁ b₂ = refl

fin-val-≢ : ∀ {n} {k l : Fin n} → Fin.value k ≢ Fin.value l → k ≢ l
fin-val-≢ x refl = x refl

_≟_ : ∀ {n} → (k l : Fin n) → Dec (k ≡ l)
mkFin kv kb ≟ mkFin lv lb with kv ℕₚ.≟ lv
... | yes kv≡lv = yes $ fin-val-≡ kv≡lv
... | no  kv≢lv = no  $ fin-val-≢ kv≢lv

-- Finite sets
record Bijection (A B : Set) : Set where
  field
    f   : A → B
    f⁻¹ : B → A
    from-to : (x : A) → f⁻¹ (f   x) ≡ x
    to-from : (x : B) → f   (f⁻¹ x) ≡ x

record FinSet : Set₁ where
  field
    type : Set
    cardinality : ℕ
    finite : Bijection type (Fin cardinality)
open FinSet

-- Sample finite sets
Σ-unit : FinSet
type Σ-unit = ⊤
cardinality Σ-unit = 1
Bijection.f (finite Σ-unit) = const $ mkFin zero $ s≤s z≤n
Bijection.f⁻¹ (finite Σ-unit) = const $ tt
Bijection.from-to (finite Σ-unit) tt = refl
Bijection.to-from (finite Σ-unit) (mkFin .0 (s≤s z≤n)) = refl

Σ-binary : FinSet
type Σ-binary = Bool
cardinality Σ-binary = 2
Bijection.f       (finite Σ-binary) false = mkFin 0 (s≤s z≤n)
Bijection.f       (finite Σ-binary) true  = mkFin 1 (s≤s (s≤s z≤n))
Bijection.f⁻¹     (finite Σ-binary) (mkFin .0 (s≤s z≤n)) = false
Bijection.f⁻¹     (finite Σ-binary) (mkFin .1 (s≤s (s≤s z≤n))) = true
Bijection.from-to (finite Σ-binary) false = refl
Bijection.from-to (finite Σ-binary) true = refl
Bijection.to-from (finite Σ-binary) (mkFin .0 (s≤s z≤n)) = refl
Bijection.to-from (finite Σ-binary) (mkFin .1 (s≤s (s≤s z≤n))) = refl

Σ-fin : ℕ → FinSet
type (Σ-fin n) = Fin n
cardinality (Σ-fin n) = n
Bijection.f       (finite (Σ-fin _)) = id
Bijection.f⁻¹     (finite (Σ-fin _)) = id
Bijection.from-to (finite (Σ-fin _)) = λ x → refl
Bijection.to-from (finite (Σ-fin _)) = λ x → refl


-- Alphabets are finite + nonempty sets,
-- strings are sequences of symbols from alphabets
_* :  FinSet → Set
Σ * = List $ type Σ

ε : ∀ {x} → x *
ε = []

_ᴿ : ∀ {x} → x * → x *
_ᴿ = reverse

_⊙_ : ∀ {x} → x * → x * → x *
_⊙_ = _++_

