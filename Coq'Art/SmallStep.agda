module SmallStep where

open import Data.Nat
open import Data.Product
  renaming (map to map×)
open import Data.Sum
  renaming (map to map⊎)

open import Relation.Nullary
open import Relation.Binary
  using (Rel)
open import Relation.Binary.PropositionalEquality

data Tm : Set where
  tm-const : (n : ℕ) → Tm
  tm-plus  : (t₁ t₂ : Tm) → Tm

module SimpleArith0 where

  eval : (t : Tm) → ℕ
  eval (tm-const n) = n
  eval (tm-plus t₁ t₂) = eval t₁ + eval t₂

module SimpleArith1 where

  -- Big-step evaluation relation

  infix 2 _⇓_

  data _⇓_ : Tm → ℕ → Set where
    e-const : ∀ {n} →
      tm-const n ⇓ n
    e-plus : ∀ {t₁ t₂ n₁ n₂} →
      t₁ ⇓ n₁ →
      t₂ ⇓ n₂ →
      tm-plus t₁ t₂ ⇓ n₁ + n₂

module SimpleArith1′ where

  -- Big-step evaluation relation

  infix 2 _⇓_

  data _⇓_ : Tm → Tm → Set where
    e-const : ∀ {n} →
      tm-const n ⇓ tm-const n
    e-plus : ∀ {t₁ t₂ n₁ n₂} →
      t₁ ⇓ tm-const n₁ →
      t₂ ⇓ tm-const n₂ →
      tm-plus t₁ t₂ ⇓ tm-const (n₁ + n₂)

module SimpleArith2 where

  -- Small-step evaluation relation

  infix 2 _⇒_

  data _⇒_ : Tm → Tm → Set where
    n+n : ∀ {n₁ n₂} →
      tm-plus (tm-const n₁) (tm-const n₂) ⇒ tm-const (n₁ + n₂)
    r+t : ∀ {t₁ t₁' t₂} →
      (t₁⇒ : t₁ ⇒ t₁') →
      tm-plus t₁ t₂ ⇒ tm-plus t₁' t₂
    n+r : ∀ {n₁ t₂ t₂'} →
      (t₂⇒ : t₂ ⇒ t₂') →
      tm-plus (tm-const n₁) t₂ ⇒ tm-plus (tm-const n₁) t₂'

  test-step-1 :
    tm-plus
      (tm-plus (tm-const 0) (tm-const 3))
      (tm-plus (tm-const 2) (tm-const 4))
    ⇒
    tm-plus
      (tm-const (0 + 3))
      (tm-plus (tm-const 2) (tm-const 4))

  test-step-1 = r+t n+n

  test-step-2 :
      tm-plus
        (tm-const 0)
        (tm-plus
          (tm-const 2)
          (tm-plus (tm-const 0) (tm-const 3)))
      ⇒
      tm-plus
        (tm-const 0)
        (tm-plus
          (tm-const 2)
          (tm-const (0 + 3)))
  test-step-2 = n+r (n+r n+n)

  -- ⇒ is deterministic

  ⇒-det : ∀ {t t′ t′′} → t ⇒ t′ → t ⇒ t′′ → t′ ≡ t′′
  ⇒-det n+n n+n = refl
  ⇒-det n+n (r+t ())
  ⇒-det n+n (n+r ())
  ⇒-det (r+t ()) n+n
  ⇒-det (r+t t₁⇒) (r+t t₁⇒′) rewrite ⇒-det t₁⇒ t₁⇒′ = refl
  ⇒-det (r+t ()) (n+r t₂⇒)
  ⇒-det (n+r ()) n+n
  ⇒-det (n+r t₂⇒) (r+t ())
  ⇒-det (n+r t₂⇒) (n+r t₂⇒') rewrite ⇒-det t₂⇒ t₂⇒' = refl


data value : Tm → Set where
  v-const : ∀ {n} → value (tm-const n)

infix 2 _⇒_

data _⇒_ : Tm → Tm → Set where
  n+n : ∀ {n₁ n₂} →
    tm-plus (tm-const n₁) (tm-const n₂) ⇒ tm-const (n₁ + n₂)
  r+t : ∀ {t₁ t₁' t₂} →
    (t₁⇒ : t₁ ⇒ t₁') →
    tm-plus t₁ t₂ ⇒ tm-plus t₁' t₂
  n+r : ∀ {t₁ t₂ t₂'} →
    value t₁ →
    (t₂⇒ : t₂ ⇒ t₂') →
    tm-plus t₁ t₂ ⇒ tm-plus t₁ t₂'

test-step-2 :
    tm-plus
      (tm-const 0)
      (tm-plus
        (tm-const 2)
        (tm-plus (tm-const 0) (tm-const 3)))
    ⇒
    tm-plus
      (tm-const 0)
      (tm-plus
        (tm-const 2)
        (tm-const (0 + 3)))
test-step-2 = n+r v-const (n+r v-const n+n)


_+V+_ : ∀ {t₁ t₂} → (v₁ : value t₁) → (v₂ : value t₂) →
         ∃ λ t′ → tm-plus t₁ t₂ ⇒ t′
v-const {n₁} +V+ v-const {n₂} = tm-const (n₁ + n₂) , n+n

⇒-det : ∀ {t t′ t′′} → t ⇒ t′ → t ⇒ t′′ → t′ ≡ t′′
⇒-det n+n n+n = refl
⇒-det n+n (r+t ())
⇒-det n+n (n+r v-const ())
⇒-det (r+t ()) n+n
⇒-det (r+t t₁⇒) (r+t t₁⇒') rewrite ⇒-det t₁⇒ t₁⇒' = refl
⇒-det (r+t ()) (n+r v-const t₂⇒)
⇒-det (n+r v-const ()) n+n
⇒-det (n+r v-const t₂⇒) (r+t ())
⇒-det (n+r _ t₂⇒) (n+r _ t₂⇒') rewrite ⇒-det t₂⇒ t₂⇒' = refl

strong-progress : ∀ t → value t ⊎ (∃ λ t' → t ⇒ t')
strong-progress (tm-const n) = inj₁ v-const
strong-progress (tm-plus t₁ t₂) =
  inj₂ (helper (strong-progress t₁) (strong-progress t₂))
  where
    helper : value t₁ ⊎ (∃ λ t' → t₁ ⇒ t') →
             value t₂ ⊎ (∃ λ t' → t₂ ⇒ t') →
             ∃ (λ t′ → tm-plus t₁ t₂ ⇒ t′)
    helper (inj₁ v₁) (inj₁ v₂) = v₁ +V+ v₂
    helper (inj₁ v₁) (inj₂ (t₂′ , t₂⇒t₂′)) = tm-plus t₁ t₂′ , n+r v₁ t₂⇒t₂′
    helper (inj₂ (t₁′ , t₁⇒t₁′)) q = tm-plus t₁′ t₂ , r+t t₁⇒t₁′

normal-form : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) (t : X) → Set ℓ
normal-form R t = ¬ (∃ λ t' → R t t')

--
