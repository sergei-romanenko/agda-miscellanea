module STLC-Parametric where

open import Data.Unit
open import Data.Bool
open import Data.Nat

open import Function

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  bool :  Ty
  _⇒_ : (α β : Ty) → Ty

⟦_⟧ : Ty → Set
⟦ bool ⟧ = Bool
⟦ α ⇒ β ⟧ = ⟦ α ⟧ → ⟦ β ⟧

--
-- Terms.
--

infixr 3 ƛ_
infixl 5 _∙_

data Tm (V : Ty → Set) : Ty → Set where
  true  : Tm V bool
  false : Tm V bool
  ⟪_⟫ : ∀ {α} (v : V α) → Tm V α
  ƛ_ : ∀ {α β} (f : V α → Tm V β) → Tm V (α ⇒ β)
  _∙_ : ∀ {α β} (f : Tm V (α ⇒ β)) (x : Tm V α) → Tm V β

Tm0 : Set₁
Tm0 = ∀ V α → Tm V α

Tm1 : Set₁
Tm1 = ∀ V α (x : V α) → Tm V α

-- I = λ x → x
I : ∀ {V α} → Tm V (α ⇒ α)
I = ƛ (λ x → ⟪ x ⟫)

-- K = λ x y → x
K : ∀ {V α β} → Tm V (α ⇒ β ⇒ α)
K = ƛ (λ x → ƛ (λ y → ⟪ x ⟫))

-- S = λ x y z → (x ∙ z) ∙ (y ∙ z)
S : ∀ {V α β γ} → Tm V ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
S = ƛ (λ x → ƛ (λ y → ƛ (λ z → (⟪ x ⟫ ∙ ⟪ z ⟫) ∙ (⟪ y ⟫ ∙ ⟪ z ⟫))))

-- This is not typable

-- Ω : ∀ {V α} → Tm V {!-l!}
-- Ω = (ƛ (λ x → ⟪ x ⟫ ∙ ⟪ x ⟫)) ∙ (ƛ (λ x → ⟪ x ⟫ ∙ ⟪ x ⟫))

--
-- Counting variable uses
--

numVars : ∀ {α} → Tm (const ⊤) α → ℕ
numVars true = 0
numVars false = 0
numVars ⟪ x ⟫ = 1
numVars (ƛ f) = numVars (f tt)
numVars (x ∙ y) = numVars x + numVars y

numVars0 : ∀ {α} → Tm0 → ℕ
numVars0 {α} x = numVars (x (const ⊤) α)

--
-- Testing for η-reducibility.
--

canEta′ : ∀ {α} → Tm (const Bool) α → Bool
canEta′ true = true
canEta′ false = true
canEta′ ⟪ v ⟫ = v
canEta′ (ƛ f) = canEta′ (f true)
canEta′ (x ∙ y) = canEta′ x ∧ canEta′ y

canEta : ∀ {α} → Tm (const Bool) α → Bool
canEta (ƛ f) with f false
... | x ∙ ⟪ false ⟫ = canEta′ x
... | _ = false
canEta _ = false

canEta0 : ∀ {α} (x : Tm0) → Bool
canEta0 {α} x = canEta (x (const Bool) α)

--
-- Capture-avoiding Substitution.
--

substTm : ∀ {α} → Tm (Tm ⟦_⟧) α → Tm ⟦_⟧ α
substTm true = true
substTm false = false
substTm ⟪ x ⟫ = x
substTm (ƛ f) = ƛ (λ v → substTm (f ⟪ v ⟫))
substTm (x ∙ y) = substTm x ∙ substTm y

substTm0 : ∀ {α} (f : Tm1) (x : Tm0) → Tm ⟦_⟧ α
substTm0 {α} f x = substTm (f (Tm ⟦_⟧) α (x ⟦_⟧ α))

--
-- Strong normalization.
--

eval : ∀ {α} (x : Tm ⟦_⟧ α) → ⟦ α ⟧
eval true = true
eval false = false
eval ⟪ v ⟫ = v
eval (ƛ f) = λ x → eval (f x)
eval (x ∙ y) = (eval x) (eval y)

SKK : ∀ {α β} → Tm ⟦_⟧ (α ⇒ α)
SKK {α} {β} = S ∙ K ∙ K {⟦_⟧} {α} {β}

SKK≡ : ∀ {α β} → eval (SKK {α} {β}) ≡ (λ x → x)
SKK≡ = refl

SKK∙true : ∀ {β} → Tm ⟦_⟧ bool
SKK∙true {β} = SKK {bool} {β} ∙ true

SKK∙true≡ : ∀ {β} → eval (SKK∙true {β}) ≡ true
SKK∙true≡ = refl

---
--- CPS-conversion.
---

data Ty! : Set where
  bool : Ty!
  _⇒0 : Ty! → Ty!
  _×_ : Ty! → Ty! → Ty!


⟦_⟧! : Ty → Ty!
⟦ bool ⟧! = bool
⟦ α ⇒ β ⟧! = (⟦ α ⟧! × (⟦ β ⟧! ⇒0)) ⇒0

mutual

  data Prim (V : Ty! → Set) (γ : Ty!) : (α : Ty!) → Set where 
    true  : Prim V γ bool
    false : Prim V γ bool
    ⟪_⟫   : ∀ {α} (v : V α) → Prim V γ α
    ƛ_ : ∀ {α} (f : V α → Tm! V γ) → Prim V γ (α ⇒0)
    _,_ : ∀ {α β} → V α → V β → Prim V γ (α × β)    
    proj₁ : ∀ {α β} → V (α × β) → Prim V γ α
    proj₂ : ∀ {α β} → V (α × β) → Prim V γ β


  data Tm! (V : Ty! → Set) : Ty! → Set where 
    halt : ∀ {α} (v : V α) → Tm! V α
    _∙_  : ∀ {α β} → V (α ⇒0) → V α → Tm! V β
    let⟨_⟩in_ : ∀ {α β} → Prim V β α → (V α → Tm! V β) → Tm! V β 

mutual

  letTm : ∀ {V α β} (x : Tm! V α) (k : V α → Tm! V β) → Tm! V β
  letTm (halt v) k = k v
  letTm (x ∙ y) k = x ∙ y
  letTm (let⟨ p ⟩in k′) k =
    let⟨ letPrim p k ⟩in (λ u → letTm (k′ u) k)

  letPrim : ∀ {t V α β} (p : Prim V α t) (k : V α → Tm! V β) → Prim V β t
  letPrim true k = true
  letPrim false k = false
  letPrim ⟪ v ⟫ k = ⟪ v ⟫
  letPrim (ƛ f) k = ƛ (λ u → letTm (f u) k)
  letPrim (u , v) k = u , v
  letPrim (proj₁ u) k = proj₁ u
  letPrim (proj₂ u) k = proj₂ u

cpsTm : ∀ {α V} (x : Tm (V ∘ ⟦_⟧!) α) → Tm! V (⟦ α ⟧!)
cpsTm true = let⟨ true ⟩in halt
cpsTm false = let⟨ false ⟩in halt
cpsTm ⟪ v ⟫ = halt v
cpsTm (ƛ f) =
  let⟨
    ƛ (λ p →
      let⟨ proj₁ p ⟩in (λ x! →
      let⟨ proj₂ p ⟩in (λ k →
        letTm (cpsTm (f x!)) (λ r →
          k ∙ r))))
  ⟩in halt
cpsTm (x ∙ y) =
  letTm (cpsTm x) (λ x! →
  letTm (cpsTm y) (λ y! →
    let⟨ ƛ halt ⟩in (λ k →
    let⟨ y! , k ⟩in (λ p →
      x! ∙ p))))

