module NatInd where

  open import Data.Nat

  open import Induction
  open import Induction.Nat

  module half-<-rec where

    {-
    <-rec : (P : ℕ → Set) →
      ((x : ℕ) → ((y : ℕ) → y <′ x → P y) → P x) →
      (x : ℕ) → P x
    -}

    half : ℕ → ℕ
    half = <-rec (λ _ → ℕ) helper
      where
      helper : (n : ℕ) → ((m : ℕ) → m <′ n → ℕ) → ℕ
      helper zero f = zero
      helper (suc zero) f = zero
      helper (suc (suc n)) f = suc (f n (≤′-step ≤′-refl))

    {-
    <-rec′ : (P : ℕ → Set) →
      ((x : ℕ) → ((y : ℕ) → y <′ x → P y) → P x) →
      (x : ℕ) → P x
    <-rec′ P f n = {!!}
    -}

  module factor-nonterminating where

    -- http://playingwithpointers.com/archives/867

    open import Data.Fin as F
    open import Data.List
    open import Data.Nat
    open import Data.Nat.DivMod

    factor : (n : ℕ) → List ℕ
    factor 0 = 0 ∷ []
    factor 1 = []
    factor (suc (suc n)) = helper n
      where helper : (try : ℕ) → List ℕ
            -- Check if (try + 1) divides (suc (suc n))
            helper 0 = (suc (suc n)) ∷ []
            helper (suc f) with ((suc (suc n)) divMod' (suc (suc f)))
            ... | result q F.zero _ = q ∷ factor (suc (suc f))
            ... | _ = helper f


  module factor-idiomatic where

    open import Data.Fin as F
    open import Induction.WellFounded
    open import Induction.Nat
    open import Data.List
    open import Data.Nat
    open import Data.Nat.DivMod
    open import Data.Nat.Properties

    factor : (n : ℕ) → Acc _<′_ n → List ℕ
    factor 0 _ = 0 ∷ []
    factor 1 _ = []
    factor (suc (suc n)) (acc p) = helper n ≤′-refl
      where
        helper : (try : ℕ) → suc try <′ suc (suc n) → List ℕ

        helper zero proof = suc (suc n) ∷ []
        helper (suc f) proof with suc (suc n) divMod' suc (suc f)
        ... | result q F.zero _ =
          q ∷ factor (suc (suc f)) (p (suc (suc f)) proof)
        ... | _ = helper f (≤⇒≤′ (≤-pred (≤′⇒≤ (≤′-step proof))))

    factorize : ℕ → List ℕ
    factorize n = factor n (<-well-founded n)

    factors₃₀ = factorize 30

--
