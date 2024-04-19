{-# OPTIONS --allow-unsolved-metas #-}
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
open import Data.Sum.Base as Sum using
  (_⊎_; inj₁; inj₂)
open import Data.Product using
  (_×_; _,′_)
open import Data.Fin as Fin using
  (Fin; _≟_)

import Data.Nat.Properties as ℕₚ

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
    ∣_∣ : ℕ
    type : Set
    finite : Bijection type (Fin ∣_∣)
open FinSet

-- Shorthand for the numbering function
Σf : ∀ Σ → type Σ → Fin ∣ Σ ∣
Σf s = Bijection.f $ finite s

Σf⁻¹ : ∀ Σ → Fin ∣ Σ ∣ → type Σ
Σf⁻¹ s = Bijection.f⁻¹ $ finite s

-- Two elements of a finite set are equal iff their mappings are equal
Σval≡ : (s : FinSet) → (a : type s) → (b : type s) → Σf s a ≡ Σf s b → a ≡ b
Σval≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) a b x with ft a | ft b
Σval≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) a b x | fta | ftb with f a | f b
Σval≡ (mkFinSet t c (↔ f f⁻¹ ft tf)) .(f⁻¹ fa) b refl | refl | ftb | fa | .fa = ftb

Σval≢ : (s : FinSet) → (a : type s) → (b : type s) → Σf s a ≢ Σf s b → a ≢ b
Σval≢ (mkFinSet t c (↔ f f⁻¹ ft tf)) a .a neq refl = neq refl

-- Anything in a finite set has decidable equality
Σ≟ : (s : FinSet) → (a : type s) → (b : type s) → Dec (a ≡ b)
Σ≟ s@(mkFinSet t c (↔ f f⁻¹ ft tf)) a b with f a ≟ f b
... | no  proof = no  $ Σval≢ s a b proof
... | yes proof = yes $ Σval≡ s a b proof

-- Closure under union
Σ∪ : FinSet → FinSet → FinSet
∣ Σ∪ a b ∣ = ∣ a ∣ + ∣ b ∣
type (Σ∪ a b) = type a ⊎ type b
Bijection.f (finite (Σ∪ a b)) = Fin.join ∣ a ∣ ∣ b ∣ ∘ Sum.map (Σf a) (Σf b)
Bijection.f⁻¹ (finite (Σ∪ a b)) = Sum.map (Σf⁻¹ a) (Σf⁻¹ b) ∘ Fin.splitAt ∣ a ∣
Bijection.from-to (finite (Σ∪ a b)) x = {!!}
Bijection.to-from (finite (Σ∪ a b)) x = {!!}

-- Closure under cartesian product
Σ× : FinSet → FinSet → FinSet
∣ Σ× a b ∣ = ∣ a ∣ * ∣ b ∣
type (Σ× a b) = type a × type b
Bijection.f (finite (Σ× a b)) = {!!}
Bijection.f⁻¹ (finite (Σ× a b)) = {!!}
Bijection.from-to (finite (Σ× a b)) = {!!}
Bijection.to-from (finite (Σ× a b)) = {!!}

-- Sample finite sets
Σ-unit : FinSet
∣ Σ-unit ∣ = 1
type Σ-unit = ⊤
Bijection.f       (finite Σ-unit) = const $ Fin.zero
Bijection.f⁻¹     (finite Σ-unit) = const $ tt
Bijection.from-to (finite Σ-unit) tt = refl
Bijection.to-from (finite Σ-unit) Fin.zero = refl

Σ-binary : FinSet
∣ Σ-binary ∣ = 2
type Σ-binary = Bool
Bijection.f       (finite Σ-binary) false = Fin.zero
Bijection.f       (finite Σ-binary) true  = Fin.suc Fin.zero
Bijection.f⁻¹     (finite Σ-binary) Fin.zero = false
Bijection.f⁻¹     (finite Σ-binary) (Fin.suc Fin.zero) = true
Bijection.from-to (finite Σ-binary) false = refl
Bijection.from-to (finite Σ-binary) true = refl
Bijection.to-from (finite Σ-binary) Fin.zero = refl
Bijection.to-from (finite Σ-binary) (Fin.suc Fin.zero) = refl

Σ-fin : ℕ → FinSet
∣ Σ-fin n ∣ = n
type (Σ-fin n) = Fin n
Bijection.f       (finite (Σ-fin _)) = id
Bijection.f⁻¹     (finite (Σ-fin _)) = id
Bijection.from-to (finite (Σ-fin _)) = λ _ → refl
Bijection.to-from (finite (Σ-fin _)) = λ _ → refl

-- Alphabets are finite + nonempty sets,
-- strings are sequences of symbols from alphabets
_* :  FinSet → Set
Σ * = List $ type Σ

ε : ∀ {x} → x *
ε = []
