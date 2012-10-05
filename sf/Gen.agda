open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding([_])

open ≡-Reasoning

module Gen where

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

inv-suc : ∀{n m : ℕ} → suc n ≡ suc m → n ≡ m
inv-suc refl = refl

double-injective₁ : (n m : ℕ) → double n ≡ double m → n ≡ m
-- P n ⟺ ∀ m → double n ≡ double m → n ≡ m
-- Consider P 0 ⟺ ∀ m → double 0 ≡ double m → 0 ≡ m
-- Suppose m ≡ 0
-- Then P 0 ⟺ 0 ≡ 0 → 0 ≡ 0
double-injective₁ zero zero _ = refl
-- Suppose m ≡ suc m'
-- Then P 0 ⟺ 0 ≡ suc (suc (double m')) → 0 ≡ suc m'
double-injective₁ zero (suc m) ()
-- Consider P (suc n') ⟺ ∀ m → double (suc n') ≡ double m → suc n' ≡ m
-- Suppose m ≡ 0
-- Then P (suc n') ⟺ suc (suc (double n')) ≡ 0 → suc n' ≡ 0
double-injective₁ (suc n') zero ()
-- Suppose m ≡ suc m'
-- Then P (suc n') ⟺ suc (suc (double n')) ≡ suc (suc (double m')) →
--                   suc n' ≡ suc m'
-- Let ssd : suc (suc (double n')) ≡ suc (suc (double m'))
-- Then inv-suc ssdn : suc (double n') ≡ suc (double m')
-- Then inv-suc (inv-suc ssdn) : double n' ≡ double m'
-- Let d : double n' ≡ double m'
-- Then double-injective₁ n' m' d : n' ≡ m'
-- Hence suc n' ≡ suc m'
double-injective₁ (suc n') (suc m') ssd with inv-suc (inv-suc ssd)
... | d = cong suc (double-injective₁ n' m' d)

double-injective₂ : (n m : ℕ) → double n ≡ double m → n ≡ m
double-injective₂ zero zero _ = refl
double-injective₂ zero (suc n) ()
double-injective₂ (suc n') zero ()
double-injective₂ (suc n') (suc m') ssd≡ssd = sn≡sm
  where
  ssd : suc (suc (double n')) ≡ suc (suc (double m'))
  ssd = ssd≡ssd
  sd : suc (double n') ≡ suc (double m')
  sd = inv-suc ssd
  d : double n' ≡ double m'
  d = inv-suc sd
  n≡m : n' ≡ m'
  n≡m = double-injective₂ n' m' d
  sn≡sm : suc n' ≡ suc m'
  sn≡sm = cong suc n≡m

