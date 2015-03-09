{-# OPTIONS --no-positivity-check #-}

module STLC-Negative where

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  bool :  Ty
  _⇒_ : (α β : Ty) → Ty

--
-- Terms.
--

infixl 5 _∙_
infixr 3 ƛ_

data Tm : Ty → Set where
  true  : Tm bool
  false : Tm bool
  ƛ_ : ∀ {α β} (f : Tm α → Tm β) → Tm (α ⇒ β)
  _∙_ : ∀ {α β} (f : Tm (α ⇒ β)) (x : Tm α) → Tm β


-- I = λ x → x
I : ∀ {α} → Tm (α ⇒ α)
I = ƛ (λ x → x)

-- K = λ x y → x
K : ∀ {α β} → Tm (α ⇒ β ⇒ α)
K = ƛ (λ x → ƛ (λ y → x))

-- S = λ x y z → (x ∙ z) ∙ (y ∙ z)
S : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
S = ƛ (λ x → ƛ (λ y → ƛ (λ z → (x ∙ z) ∙ (y ∙ z))))

-- This is not typable... :-(

-- Ω : Tm
-- Ω = (ƛ (λ x → x ∙ x)) ∙ (ƛ (λ x → x ∙ x))

--
-- Strong normalization.
--

{-# NON_TERMINATING #-}
mutual

  infixl 5 _⟨∙⟩_

  _⟨∙⟩_ : ∀ {α β} (f : Tm (α ⇒ β)) (x : Tm α) → Tm β
  (ƛ f) ⟨∙⟩ x = eval (f x)
  (f ∙ x′) ⟨∙⟩ x = (f ∙ x′) ∙ x

  eval : ∀ {α} (x : Tm α) → Tm α
  eval true = true
  eval false = false
  eval (ƛ f) = ƛ f
  eval (f ∙ x) = eval f ⟨∙⟩ eval x


SKK : ∀ {α β} → Tm (α ⇒ α)
SKK {α} {β} = S ∙ K ∙ K {α} {β}

-- Try ctrl-c ctrl-n SKK∙true
-- The result will be true.

SKK∙true : ∀ {β} → Tm bool
SKK∙true {β} = eval (SKK {bool} {β} ∙ true)

-- Try ctrl-c ctrl-n SKK∙true
-- The result will be λ {β} → true.
