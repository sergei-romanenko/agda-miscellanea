module WellFounded-Log2 where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function

open import Induction.WellFounded
open import Induction.Nat


div2 : ℕ → ℕ

div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

module log2-bad where

  log2 : ℕ → ℕ

  log2 zero = zero
  log2 (suc zero) = zero
  log2 (suc (suc n)) = suc (log2 (suc (div2 n)))

  log2-0 : log2 0 ≡ zero
  log2-0 = refl

  log2-2 : log2 2 ≡ 1
  log2-2 = refl

  log2-4 : log2 4 ≡ 2
  log2-4 = refl

--
-- Well-founded induction
--

wf-induction : ∀ {ℓ} {A : Set ℓ} (_<_ : Rel A ℓ) → Well-founded _<_ →
  (P : A → Set ℓ) →
  (step : ∀ x → (∀ y → y < x → P y) → P x) →
  ∀ x → P x
wf-induction _<_ wf P step x = helper x (wf x)
  where
    helper : ∀ x → Acc _<_ x → P x
    helper x (acc rs) = step x (λ y y<x → helper y (rs y y<x))

div2n≤′n : (n : ℕ) → div2 n ≤′ n

div2n≤′n zero = ≤′-refl
div2n≤′n (suc zero) = ≤′-step ≤′-refl
div2n≤′n (suc (suc n)) = s≤′s (≤′-step (div2n≤′n n))

module log2-good where

  log2′ : (n : ℕ) → Acc _<′_ n → ℕ
  log2′ zero (acc rs) = zero
  log2′ (suc zero) (acc rs) = zero
  log2′ (suc (suc n)) (acc rs) =
    suc (log2′ n′ (rs n′ (n′ <′ suc (suc n) ∋ n′<′)))
    where
      n′ = suc (div2 n)
      n′<′ = (s≤′s (s≤′s (div2n≤′n n)))

  log2 : ℕ → ℕ
  log2 n = log2′ n (<-well-founded n)

  log2-0 : log2 0 ≡ zero
  log2-0 = refl

  log2-2 : log2 2 ≡ 1
  log2-2 = refl

  log2-3 : log2 3 ≡ 1
  log2-3 = refl

  log2-4 : log2 4 ≡ 2
  log2-4 = refl


--
