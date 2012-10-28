module StructRec where

open import Data.Nat
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

n≤sn : ∀ n → n ≤ suc n
n≤sn zero = z≤n
n≤sn (suc n) = s≤s (n≤sn n)

module div2-≤₁ where 

  div2-≤ : ∀ n → div2 n ≤ n
  div2-≤ zero = z≤n
  div2-≤ (suc zero) = z≤n
  div2-≤ (suc (suc n)) = s≤s d2n≤sn
    where open ≤-Reasoning
          d2n≤sn : div2 n ≤ suc n
          d2n≤sn = begin 
                     div2 n ≤⟨ div2-≤ n ⟩
                     n      ≤⟨ n≤sn n ⟩
                     suc n
                   ∎

module div2-≤₂ where 

  s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
  s≤′s ≤′-refl = ≤′-refl
  s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

  div2-≤ : ∀ n → div2 n ≤′ n
  div2-≤ zero = ≤′-refl
  div2-≤ (suc zero) = ≤′-step ≤′-refl
  div2-≤ (suc (suc n)) = ≤′-step (s≤′s (div2-≤ n))

module div2-≤₃ where

  div2-≤₀ : ∀ n → (div2 n ≤ n) × (div2 (suc n) ≤ suc n)
  div2-≤₀ zero = z≤n , z≤n
  div2-≤₀ (suc zero) = z≤n , s≤s z≤n
  div2-≤₀ (suc (suc n)) = s≤s prop₁ , s≤s prop₂
    where open ≤-Reasoning
          prop₁ : div2 n ≤ suc n
          prop₁ = begin
                    div2 n ≤⟨ proj₁ (div2-≤₀ n) ⟩
                    n ≤⟨ n≤sn n ⟩
                    suc n
                  ∎
          prop₂ : div2 (suc n) ≤ suc (suc n)
          prop₂ = begin
                    div2 (suc n) ≤⟨ proj₂ (div2-≤₀ n) ⟩
                    suc n ≤⟨ s≤s (n≤sn n) ⟩
                    suc (suc n)
                  ∎

  div2-≤ : ∀ n → (div2 n ≤ n)
  div2-≤ n = proj₁ (div2-≤₀ n)


nat-ind : ∀ {P : ℕ → Set} → P zero → (∀ n → P n → P (suc n)) →
            (∀ n → P n)
nat-ind base step zero = base
nat-ind base step (suc n) = step n (nat-ind base step n)

nat-ind-2 : ∀ {P Q : ℕ → Set} → P zero → Q zero →
              (∀ n → P n → Q n → P (suc n)) →
              (∀ n → P n → Q n → Q (suc n)) →
            (∀ n → P n × Q n)
nat-ind-2 p-base q-base p-step q-step zero = p-base , q-base
nat-ind-2 p-base q-base p-step q-step (suc n)
        with nat-ind-2 p-base q-base p-step q-step n
... | p-n , q-n = p-step n p-n q-n , q-step n p-n q-n


module div2-≤₄ where

  div2-≤₀ : ∀ n → div2 n ≤ n × div2 (suc n) ≤ suc n
  div2-≤₀ n =
    nat-ind-2 z≤n z≤n 
              (λ n p q → q)
              (λ n p q → s≤s (
                begin
                  div2 n ≤⟨ p ⟩
                  n ≤⟨ n≤sn n ⟩
                  suc n
                ∎))
              n
    where open ≤-Reasoning

nat-2-ind : ∀ {P : ℕ → Set} → P zero → P (suc zero) →
              (∀ n → P n → P (suc (suc n))) →
              (∀ n → P n)
nat-2-ind base0 base1 step zero = base0
nat-2-ind base0 base1 step (suc zero) = base1
nat-2-ind base0 base1 step (suc (suc n)) =
  step n (nat-2-ind base0 base1 step n)

module div2-≤₅ where 

  div2-≤ : ∀ n → div2 n ≤ n
  div2-≤ n = nat-2-ind z≤n z≤n step n
    where step : ∀ n (p : div2 n ≤ n) → suc (div2 n) ≤ suc (suc n) 
          step n p = s≤s d2n≤sn
            where open ≤-Reasoning
                  d2n≤sn : div2 n ≤ suc n
                  d2n≤sn = begin 
                             div2 n ≤⟨ p ⟩
                             n      ≤⟨ n≤sn n ⟩
                             suc n
                           ∎

_+′_ : ℕ → ℕ → ℕ
zero  +′ n = n
suc m +′ n = m +′ suc n

m+′sn : ∀ m n → m +′ suc n ≡ suc (m +′ n)
m+′sn zero n = refl
m+′sn (suc m) n = m+′sn m (suc n)
