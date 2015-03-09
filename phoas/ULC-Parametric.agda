module ULC-Parametric where

open import Data.Unit
open import Data.Bool
open import Data.Nat

infixl 5 _∙_
infixr 3 ƛ_

--
-- Terms.
--

data Tm (V : Set) : Set where
  true  : Tm V
  false : Tm V
  ⟪_⟫ : V → Tm V
  ƛ_ : (V → Tm V) → Tm V
  _∙_ : Tm V → Tm V → Tm V

Tm0 : Set₁
Tm0 = ∀ {V} → Tm V

Tm1 : Set₁
Tm1 = ∀ {V} (x : V) → Tm V 

-- I = λ x → x
I : ∀ {V} → Tm V
I = ƛ (λ x → ⟪ x ⟫)

-- K = λ x y → x
K : ∀ {V} → Tm V
K = ƛ (λ x → ƛ (λ y → ⟪ x ⟫))

-- S = λ x y z → (x ∙ z) ∙ (y ∙ z)
S : ∀ {V} → Tm V
S = ƛ (λ x → ƛ (λ y → ƛ (λ z → (⟪ x ⟫ ∙ ⟪ z ⟫) ∙ (⟪ y ⟫ ∙ ⟪ z ⟫))))

Ω : ∀ {V} → Tm V
Ω = (ƛ (λ x → ⟪ x ⟫ ∙ ⟪ x ⟫)) ∙ (ƛ (λ x → ⟪ x ⟫ ∙ ⟪ x ⟫))

--
-- Counting variable uses
--

numVars : Tm ⊤ → ℕ
numVars true = 0
numVars false = 0
numVars ⟪ x ⟫ = 1
numVars (ƛ f) = numVars (f tt)
numVars (x ∙ y) = numVars x + numVars y

numVars0 : Tm0 → ℕ
numVars0 x = numVars x

--
-- Testing for η-reducibility.
--

canEta′ : Tm Bool → Bool
canEta′ true = true
canEta′ false = true
canEta′ ⟪ b ⟫ = b
canEta′ (ƛ f) = canEta′ (f true)
canEta′ (x ∙ y) = canEta′ x ∧ canEta′ y

canEta : Tm Bool → Bool
canEta (ƛ f) with f false
... | x ∙ ⟪ false ⟫ = canEta′ x
... | _ = false
canEta _ = false

canEta0 : Tm0 → Bool
canEta0 x = canEta x

--
-- Capture-avoiding Substitution.
--

substTm : ∀ {V} → Tm (Tm V) → Tm V
substTm true = true
substTm false = false
substTm ⟪ x ⟫ = x
substTm (ƛ f) = ƛ (λ v → substTm (f ⟪ v ⟫))
substTm (x ∙ y) = substTm x ∙ substTm y

substTm0 : Tm1 → Tm0 → Tm0
substTm0 x y = substTm (x y)

--
-- Call by value.
--

{-# NON_TERMINATING #-}
mutual

  infixl 5 _⟨∙⟩_

  _⟨∙⟩_ : ∀ {V} → Tm V → Tm V → Tm V
  true ⟨∙⟩ y = true ∙ y
  false ⟨∙⟩ y = false ∙ y
  ⟪ x ⟫ ⟨∙⟩ y = ⟪ x ⟫ ∙ y
  (ƛ f) ⟨∙⟩ y = eval {!f y!}
  (x ∙ x′) ⟨∙⟩ y = (x ∙ x′) ∙ y

  eval : ∀ {V} → Tm (Tm V) → Tm V
  eval true = true
  eval false = false
  eval ⟪ v ⟫ = v
  --eval (ƛ f) = ƛ (λ x → eval (f ⟪ x ⟫))
  eval (ƛ f) = {!!}
  eval (x ∙ y) = eval x ⟨∙⟩ eval y --eval x ⟨∙⟩ eval y


-- SKK : ∀ {α β} → Tm (α ⇒ α)
-- SKK {α} {β} = S ∙ K ∙ K {α} {β}

-- -- Try ctrl-c ctrl-n SKK∙true
-- -- The result will be true.

-- SKK∙true : ∀ {β} → Tm bool
-- SKK∙true {β} = eval (SKK {bool} {β} ∙ true)

-- -- Try ctrl-c ctrl-n SKK∙true
-- -- The result will be λ {β} → true.
