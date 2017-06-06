open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Product as Prod
open import Data.Sum
open import Function using (_∘_; id)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

module Subset where

ex-diff : ∀ {m n} → m ≤ n →  ∃ λ x → m + x ≡ n
--ex-diff : {m n : ℕ} → m ≤ n → Σ ℕ (λ x → m + x ≡ n)
ex-diff (z≤n {n}) = n , refl
ex-diff (s≤s m≤n) with ex-diff m≤n
... | x , p = x , cong suc p

ex-diff₂ : ∀ {m n} → m ≤ n → ∃ λ x → m + x ≡ n
ex-diff₂ (z≤n {n}) = n , refl
ex-diff₂ (s≤s m≤n) =
  Prod.map id (cong suc) (ex-diff₂ m≤n)

pred₁ : (n : ℕ) → 1 ≤ n  → ℕ
pred₁ zero 1≤n = zero
pred₁ (suc n) 1≤n = n

pred₂ : (s : Σ ℕ (λ n → 1 ≤ n)) → ℕ
pred₂ (zero , 1≤n) = zero
pred₂ (suc n , 1≤n) = n

pred₃ : (s : Σ ℕ (λ n → 1 ≤ n)) → Σ ℕ (λ m → m ≡ suc (proj₁ s))
pred₃ (n , 1≤n) = suc n , refl

pred₅ : (n : ℕ) → Σ ℕ (λ m → n ≡ suc m) ⊎ n ≡ 0
pred₅ zero = inj₂ refl
pred₅ (suc n) = inj₁ (n , refl)

pred₇ : (n : ℕ) → Maybe (Σ ℕ (λ m → n ≡ suc m))
pred₇ zero = nothing
pred₇ (suc n) = just (n , refl)

pred₈ : (n : ℕ) → 1 ≤ n  → Σ ℕ (λ m → n ≡ suc m)
pred₈ zero ()
pred₈ (suc n) 1≤n = n , refl

pred-strong₇ : (n : ℕ) → (m : ℕ) → Dec(n ≡ suc m)
pred-strong₇ zero m = no (λ ())
pred-strong₇ (suc zero) zero = yes refl
pred-strong₇ (suc (suc n)) zero = no (λ ())
pred-strong₇ (suc n) (suc m) with pred-strong₇ n m
pred-strong₇ (suc n) (suc m) | yes n≡sm = yes (cong suc n≡sm)
pred-strong₇ (suc n) (suc m) | no  n≢sm = no (n≢sm ∘ cong pred)

pred₉ : (n : ℕ) → Dec(Σ ℕ (λ m → n ≡ suc m))
pred₉ zero = no 0≢m+1 where
  0≢m+1 : Σ ℕ (λ m → 0 ≡ suc m) → ⊥
  0≢m+1 (m , ())
pred₉ (suc n) = yes (n , refl)

-- A Type-Checking Example

data Exp : Set where
  nat  : ℕ → Exp
  plus : Exp → Exp → Exp
  bool : Bool → Exp
  and  : Exp → Exp → Exp

data Type : Set where
  nat  : Type
  bool : Type

data ⊢_∈_ : Exp → Type → Set where
  nat∈  : ∀ {n} → ⊢ nat n ∈ nat
  plus∈ : ∀ {e₁ e₂} → ⊢ e₁ ∈ nat → ⊢ e₂ ∈ nat →
             ⊢ plus e₁ e₂ ∈ nat
  bool∈ : ∀ {b} → ⊢ bool b ∈ bool

  and∈  : ∀ {e₁ e₂} → ⊢ e₁ ∈ bool → ⊢ e₂ ∈ bool →
             ⊢ and e₁ e₂ ∈ bool

plus∈₁ : ∀ {e₁ e₂} → ⊢ plus e₁ e₂ ∈ nat → ⊢ e₁ ∈ nat
plus∈₁ (plus∈ p q) = p

plus∈₂ : ∀ {e₁ e₂} → ⊢ plus e₁ e₂ ∈ nat → ⊢ e₂ ∈ nat
plus∈₂ (plus∈ p q) = q

and∈₁ : ∀ {e₁ e₂} → ⊢ and e₁ e₂ ∈ bool → ⊢ e₁ ∈ bool
and∈₁ (and∈ p q) = p

and∈₂ : ∀ {e₁ e₂} → ⊢ and e₁ e₂ ∈ bool → ⊢ e₂ ∈ bool
and∈₂ (and∈ p q) = q

⊢?_∈_ : (e : Exp) → (τ : Type) →  Dec (⊢ e ∈ τ)
⊢? nat n ∈ nat = yes nat∈
⊢? nat n ∈ bool = no (λ ())
⊢? plus e₁ e₂ ∈ nat with ⊢? e₁ ∈ nat | ⊢? e₂ ∈ nat
... | yes e₁∈ | yes e₂∈ = yes (plus∈ e₁∈ e₂∈)
... | no  e₁∉ | _        = no (e₁∉ ∘ plus∈₁)
... | _        | no e₂∉  = no (e₂∉ ∘ plus∈₂)
⊢? plus e₁ e₂ ∈ bool = no (λ ())
⊢? bool b ∈ nat = no (λ ())
⊢? bool b ∈ bool = yes bool∈
⊢? and e₁ e₂ ∈ nat = no (λ ())
⊢? and e₁ e₂ ∈ bool with ⊢? e₁ ∈ bool | ⊢? e₂ ∈ bool
... | yes e₁∈ | yes e₂∈ = yes (and∈ e₁∈ e₂∈)
... | no  e₁∉ | _        = no (e₁∉ ∘ and∈₁)
... | _        | no  e₂∉  = no (e₂∉ ∘ and∈₂)

t01 : (⊢? nat 0 ∈ nat) ≡ yes nat∈
t01 = refl

t02 : ⊢? plus (nat 1) (nat 2) ∈ nat ≡ yes (plus∈ nat∈ nat∈)
t02 = refl

t03 : ⊢? plus (nat 1) (bool false) ∈ bool ≡ no (λ ())
t03 = refl

⊢?_ : (e : Exp) → Maybe ( Σ Type (λ τ → ⊢ e ∈ τ) )
⊢? nat n = just (nat , nat∈)
⊢? plus e₁ e₂ with ⊢? e₁ | ⊢? e₂
... | just (nat , e₁∈) | just (nat , e₂∈) = just (nat , plus∈ e₁∈ e₂∈)
... | _ | _ = nothing
⊢? bool b = just (bool , bool∈)
⊢? and e₁ e₂ with ⊢? e₁ | ⊢? e₂
... | just (bool , e₁∈) | just (bool , e₂∈) = just (bool , and∈ e₁∈ e₂∈)
... | _ | _ = nothing
