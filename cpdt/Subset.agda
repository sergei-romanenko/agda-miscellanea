open import Data.Empty
open import Data.Bool
open import Data.Nat
--open import Data.Nat.Properties
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function using ( _∘_ )

open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

module Subset where

ex-diff : (m n : ℕ) → m ≤ n → Σ ℕ (λ x → m + x ≡ n)
--ex-diff : (m n : ℕ) → m ≤ n →  ∃ λ ( x : ℕ ) → (m + x ≡ n)
ex-diff zero n m≤n = n , refl
ex-diff (suc m) .(suc n) (s≤s {.m} {n} m≤n) with ex-diff m n m≤n
... | x , p = x , cong suc p

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

inv-suc : ∀ {n m} -> suc n ≡ suc m → n ≡ m
inv-suc refl = refl

pred-strong₇ : (n : ℕ) → (m : ℕ) -> Dec(n ≡ suc m)
pred-strong₇ zero m = no (λ ())
pred-strong₇ (suc zero) zero = yes refl
pred-strong₇ (suc (suc n)) zero = no (λ ())
pred-strong₇ (suc n') (suc m') with pred-strong₇ n' m'
pred-strong₇ (suc n') (suc m') | yes p = yes (cong suc p)
pred-strong₇ (suc n') (suc m') | no ¬p = no (¬p ∘ inv-suc)

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

data ⊢_▷_ : Exp -> Type -> Set where
  htNat  : ∀ {n} → ⊢ nat n ▷ nat
  htPlus : ∀ {e1 e2} → ⊢ e1 ▷ nat → ⊢ e2 ▷ nat →
             ⊢ plus e1 e2 ▷ nat
  htBool : ∀ {b} → ⊢ bool b ▷ bool

  htAnd  : ∀ {e1 e2} → ⊢ e1 ▷ bool → ⊢ e2 ▷ bool →
             ⊢ and e1 e2 ▷ bool

inv-htPlus-1 : ∀ (e1 e2 : Exp) → ⊢ plus e1 e2 ▷ nat → ⊢ e1 ▷ nat
inv-htPlus-1 e1 e2 (htPlus p q) = p

inv-htPlus-2 : ∀ (e1 e2 : Exp) → ⊢ plus e1 e2 ▷ nat → ⊢ e2 ▷ nat
inv-htPlus-2 e1 e2 (htPlus p q) = q

inv-htAnd-1 : ∀ (e1 e2 : Exp) → ⊢ and e1 e2 ▷ bool → ⊢ e1 ▷ bool
inv-htAnd-1 e1 e2 (htAnd p q) = p

inv-htAnd-2 : ∀ (e1 e2 : Exp) → ⊢ and e1 e2 ▷ bool → ⊢ e2 ▷ bool
inv-htAnd-2 e1 e2 (htAnd p q) = q


_≡Ty?_ : (σ τ : Type) → Dec (σ ≡ τ)
nat  ≡Ty? nat = yes refl
nat  ≡Ty? bool = no (λ ())
bool ≡Ty? nat = no (λ ())
bool ≡Ty? bool = yes refl

⊢?_▷_ : (e : Exp) → (τ : Type) →  Dec (⊢ e ▷ τ)
⊢? nat n ▷ nat = yes htNat
⊢? nat n ▷ bool = no (λ ())
⊢? plus e1 e2 ▷ nat with ⊢? e1 ▷ nat | ⊢? e2 ▷ nat
⊢? plus e1 e2 ▷ nat  | yes p | yes q = yes (htPlus p q)
⊢? plus e1 e2 ▷ nat  | _ | no ¬q =
                no (λ z → ¬q (inv-htPlus-2 e1 e2 z))
⊢? plus e1 e2 ▷ nat  | no ¬p | yes q =
                no (λ z → ¬p (inv-htPlus-1 e1 e2 z))
⊢? plus e1 e2 ▷ bool = no (λ ())
⊢? bool b ▷ nat = no (λ ())
⊢? bool b ▷ bool = yes htBool
⊢? and e1 e2 ▷ nat = no (λ ())
⊢? and e1 e2 ▷ bool with ⊢? e1 ▷ bool | ⊢? e2 ▷ bool
⊢? and e1 e2 ▷ bool | yes p | yes p' = yes (htAnd p p')
⊢? and e1 e2 ▷ bool | yes p | no ¬p =
               no (λ z → ¬p (inv-htAnd-2 e1 e2 z))
⊢? and e1 e2 ▷ bool | no ¬p | _ =
               no (λ z → ¬p (inv-htAnd-1 e1 e2 z))

t01 : (⊢? nat 0 ▷ nat) ≡ yes htNat
t01 = refl

t02 : ⊢? plus (nat 1) (nat 2) ▷ nat ≡ yes (htPlus htNat htNat)
t02 = refl

t03 : ⌊ ⊢? plus (nat 1) (bool false) ▷ bool ⌋ ≡ false
t03 = refl
