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
open import Data.Sum.Base using
  (_⊎_; inj₁; inj₂)

import Data.Nat.Properties as ℕₚ

-- Finite natural numbers
record Fin (n : ℕ) : Set where
  constructor mkFin
  field
    value : ℕ
    bounded : value < n

-- Addition
_fin+_ : ∀ {n m} → Fin n → Fin m → Fin (n + m)
_fin+_ {n} {m} (mkFin v₁ b₁) (mkFin v₂ b₂) rewrite ℕₚ.+-comm m n = mkFin (v₁ + v₂) {!!}

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
  constructor ↔
  field
    f   : A → B
    f⁻¹ : B → A
    from-to : (x : A) → f⁻¹ (f   x) ≡ x
    to-from : (x : B) → f   (f⁻¹ x) ≡ x

record FinSet : Set₁ where
  constructor mkFinSet
  field
    type : Set
    cardinality : ℕ
    finite : Bijection type (Fin cardinality)
open FinSet

Σnumbering : ∀ Σ → type Σ → Fin (cardinality Σ)
Σnumbering s = Bijection.f $ finite s

Σnumbering⁻¹ : ∀ Σ → Fin (cardinality Σ) → type Σ
Σnumbering⁻¹ s = Bijection.f⁻¹ $ finite s

-- Elements of a finite set are equal as soon as their Fin mappings are equal
finset-≡ : (s : FinSet) → (a : type s) → (b : type s)
         → let number = Bijection.f (finite s) in (number a ≡ number b)
         → a ≡ b
finset-≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) a b x with ft a | ft b
finset-≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) a b x | fta | ftb with f a | f b
finset-≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) .(f⁻¹ fa) b refl | refl | ftb | fa | .fa = ftb

finset-≢ : (s : FinSet) → (a : type s) → (b : type s)
         → let number = Bijection.f (finite s) in (number a ≢ number b)
         → a ≢ b
finset-≢ (mkFinSet t c (↔ f f⁻¹ ft tf)) a .a neq refl = neq refl

-- Anything in a finite set has decidable equality
Σ≟ : (s : FinSet) → (a : type s) → (b : type s) → Dec (a ≡ b)
Σ≟ s@(mkFinSet t c (↔ f f⁻¹ ft tf)) a b with f a ≟ f b
... | no  proof = no  $ finset-≢ s a b proof
... | yes proof = yes $ finset-≡ s a b proof

-- Union of finite sets
Σ∪ : FinSet → FinSet → FinSet
type (Σ∪ a b) = type a ⊎ type b
cardinality (Σ∪ a b) = cardinality a + cardinality b
Bijection.f (finite (Σ∪ a b)) (inj₁ x)
  with (mkFin xv xb) ← Σnumbering a x =
    let proof = ℕₚ.m≤n⇒m≤n+o (cardinality b) xb in
    mkFin xv proof
Bijection.f (finite (Σ∪ a b)) (inj₂ y)
  with (mkFin yv yb) ← Σnumbering b y
  rewrite ℕₚ.+-comm (cardinality a) (cardinality b) =
    let shifted = yv + (cardinality a) in
    let proof = ℕₚ.+-monoˡ-< (cardinality a) yb in
    mkFin shifted proof
Bijection.f⁻¹ (finite (Σ∪ a b)) (mkFin v bnd) with v ℕₚ.<? (cardinality a)
Bijection.f⁻¹ (finite (Σ∪ a b)) (mkFin v bnd) | yes v<|a| =
  inj₁ $ Σnumbering⁻¹ a $ mkFin v v<|a|
Bijection.f⁻¹ (finite (Σ∪ a b)) (mkFin v bnd) | no  v≮|a| with ℕₚ.≰⇒> v≮|a|
Bijection.f⁻¹ (finite (Σ∪ a b)) (mkFin v bnd) | no  v≮|a| | (s≤s |a|≤v)
  with proof ← ℕₚ.∸-monoˡ-< bnd |a|≤v
  rewrite ℕₚ.m+n∸m≡n (cardinality a) (cardinality b) =
    let diff = v ∸ cardinality a in
    inj₂ $ Σnumbering⁻¹ b (mkFin diff proof)
Bijection.from-to (finite (Σ∪ a b)) = {!!}
Bijection.to-from (finite (Σ∪ a b)) = {!!}

-- Sample finite sets
Σ-unit : FinSet
type Σ-unit = ⊤
cardinality Σ-unit = 1
Bijection.f       (finite Σ-unit) = const $ mkFin zero $ s≤s z≤n
Bijection.f⁻¹     (finite Σ-unit) = const $ tt
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

