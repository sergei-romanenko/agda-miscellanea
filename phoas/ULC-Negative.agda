{-# OPTIONS --no-positivity-check #-}

module ULC-Negative where

infixl 5 _∙_
infixr 3 ƛ_

--
-- Terms.
--

data Tm : Set where
  true  : Tm
  false : Tm
  ƛ_ : (f : Tm → Tm) → Tm
  _∙_ : (f : Tm) (x : Tm) → Tm

-- I = λ x → x
I : Tm
I = ƛ (λ x → x)

-- K = λ x y → x
K : Tm
K = ƛ (λ x → ƛ (λ y → x))

-- S = λ x y z → (x ∙ z) ∙ (y ∙ z)
S : Tm
S = ƛ (λ x → ƛ (λ y → ƛ (λ z → (x ∙ z) ∙ (y ∙ z))))


Ω : Tm
Ω = (ƛ (λ x → x ∙ x)) ∙ (ƛ (λ x → x ∙ x))

--
-- Call by name.
--

{-# NON_TERMINATING #-}  
mutual

  infixl 5 _⟨∙⟩_

  _⟨∙⟩_ : (f : Tm) (x : Tm) → Tm
  (ƛ f) ⟨∙⟩ x = eval (f x)
  f ⟨∙⟩ x = f ∙ x

  eval : Tm → Tm
  eval true = true
  eval false = false
  eval (ƛ f) = ƛ f
  eval (f ∙ x) = eval f ⟨∙⟩ x

SKK : Tm
SKK = S ∙ K ∙ K

-- Try ctrl-c ctrl-n SKK∙true
-- The result will be true.

SKK∙true : Tm
SKK∙true = eval (SKK ∙ true)
