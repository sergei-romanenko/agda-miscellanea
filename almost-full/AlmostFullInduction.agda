{-
    Title:      AlmostFullInduction.Agda
    Author:     Sergei Romanenko, KIAM Moscow

    This Agda version is based on

    Dimitrios Vytiniotis, Thierry Coquand, and David Wahlstedt.   
    Stop when you are almost-full.  
    Adventures in constructive termination.  
    In Interactive Theorem Proving, ITP 2012. to appear.

    http://research.microsoft.com/en-us/people/dimitris/af-itp.pdf
    http://research.microsoft.com/en-us/people/dimitris/af-itp2012.tgz
    http://research.microsoft.com/en-us/people/dimitris/afchalmers.pptx
-}

module AlmostFullInduction where

open import Data.Nat
open import Data.Product
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′ )
  renaming (map to map⊎)
open import Data.Empty
open import Data.Star
open import Data.Plus
--open import Data.Fin
--  renaming (_≤_ to _≤F_; _<_ to _<F_; _+_ to _+F+; compare to compareF)


open import Data.Nat.Properties
  --using (≤⇒≤′; ≤′⇒≤)

open import Relation.Nullary
open import Relation.Unary
  hiding (Decidable)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function

open import Induction.WellFounded

import Level

open ≡-Reasoning

open import AlmostFull
open import AFConstructions

--
-- af_induction principle
--

-- wf-induction

wf-induction : ∀ {ℓ} {A : Set ℓ} (T : Rel A ℓ) → Well-founded T →
  (P : A → Set ℓ) →
  (g : ∀ x → (∀ y →  T y x → P y) → P x) →
  ∀ a → P a
wf-induction T wfT P g a = helper a (wfT a)
  where
    helper : ∀ u → Acc T u → P u
    helper u (acc rs) = g u (λ v r → helper v (rs v r))

-- af-induction

af-induction : ∀ {ℓ} {A : Set ℓ} (T R : Rel A ℓ) → Almost-full R → 
   (∀ x y → Plus T x y → R y x → ⊥) → 
   (P : A → Set ℓ) → (∀ x → (∀ y → T y x → P y) → P x) →
   ∀ a → P a
af-induction {A = A} T R afR disj P g =
  wf-induction T (wf-from-af T disj afR) P g

{-
  A very simple test that the fixpoint combinator /indeed/
  gives us a fixpoint
-}

-- fib

-- (1) Prove ≤′ is AF
-- (2) Prove intersection emptyness
-- (3) Give the functional

<-asym : {x y : ℕ} → x < y → y ≤ x → ⊥
<-asym (s≤s m≤n) (s≤s m≤n') = <-asym m≤n m≤n'

<′-asym : {x y : ℕ} → x <′ y → y ≤′ x → ⊥
<′-asym x<′y y≤′x = <-asym (≤′⇒≤ x<′y) (≤′⇒≤ y≤′x)

<′-trans : Transitive _<′_
<′-trans i<′j j<′k = ≤⇒≤′ (<-trans (≤′⇒≤ i<′j) (≤′⇒≤ j<′k))

<′⁺⇒<′ : (x y : ℕ) → Plus (λ m n → m <′ n) x y → x <′ y
<′⁺⇒<′ x y [ x<′y ] = x<′y
<′⁺⇒<′ x y (.x ∼⁺⟨ x<′⁺y ⟩ y<′⁺y) = <′-trans (<′⁺⇒<′ x _ x<′⁺y) (<′⁺⇒<′ _ y y<′⁺y)

∩-empty : (x y : ℕ) → Plus (λ m n → m <′ n) x y → y ≤′ x → ⊥
∩-empty x y x<⁺y y≤′x = <′-asym (<′⁺⇒<′ x y x<⁺y) y≤′x

fib : ℕ → ℕ
fib = af-induction _<′_ _≤′_ ≤′-af ∩-empty (λ _ → ℕ) step
  where

    step : (x : ℕ) → ((y : ℕ) → suc y ≤′ x → ℕ) → ℕ
    step zero f = suc zero
    step (suc zero) f = suc zero
    step (suc (suc x)) f = f (suc x) ≤′-refl + f x (≤′-step ≤′-refl)

fib0 : fib 0 ≡ 1
fib0 = refl

fib1 : fib 1 ≡ 1
fib1 = refl

fib2 : fib 2 ≡ 2
fib2 = refl

fib3 : fib 3 ≡ 3
fib3 = refl

fib4 : fib 4 ≡ 5
fib4 = refl

fib5 : fib 5 ≡ 8
fib5 = refl

--
-- A principle more akin to size-change-termination
--

-- Power of a relation

power : ∀ {ℓ} {X : Set ℓ} → (n : ℕ) (R : Rel X ℓ) → (x y : X) → Set ℓ
power zero R x y = x ≡ y
power (suc n) R x y = ∃ (λ z → (R x z) × (power n R z y))

-- Addition modulo k

plus-mod! : (k n x : ℕ) → x <′ k → ℕ
plus-mod! k zero x x<′k = x
plus-mod! .(suc x) (suc n) x ≤′-refl =
  plus-mod! (suc x) n zero (s≤′s z≤′n)
plus-mod! .(suc k') (suc n) x (≤′-step {k'} x<′k') =
  plus-mod! (suc k') n (suc x) (s≤′s x<′k')

-- Interesting lemmas about addition modulo k

-- plus-mod-aux-fin

plus-mod-fin! : (k n x : ℕ) →
  (lt : x <′ k) → plus-mod! k n x lt <′ k
plus-mod-fin! k zero x x<′k = x<′k
plus-mod-fin! .(suc x) (suc n) x ≤′-refl =
  plus-mod-fin! (suc x) n zero (s≤′s z≤′n)
plus-mod-fin! .(suc k') (suc n) x (≤′-step {k'} x<′k') =
  plus-mod-fin! (suc k') n (suc x) (s≤′s x<′k')

-- plus-mod

plus-mod : {k : ℕ} (n : ℕ) (x : Finite k) → Finite k
plus-mod {k} n (fin-intro x x<′k) =
  fin-intro (plus-mod! k n x x<′k) (plus-mod-fin! k n x x<′k)

-- plus-mod-lt

-- ≰⇒> : _≰_ ⇒ _>_

+s : (m n : ℕ) → m + suc n ≡ suc (m + n)
+s zero n = refl
+s (suc m) n = cong suc (+s m n)

≤′-pred : {m n : ℕ} → suc m ≤′ suc n → m ≤′ n
≤′-pred = ≤⇒≤′ ∘ ≤-pred ∘ ≤′⇒≤

n+x<′k⇒x<′k : (n : ℕ) {x k : ℕ} → n + x <′ k → x <′ k
n+x<′k⇒x<′k zero n+x<′k = n+x<′k
n+x<′k⇒x<′k (suc n) n+x<′k =
  n+x<′k⇒x<′k n (≤′-pred (≤′-step n+x<′k)) 

plus-mod-lt! : (k n x : ℕ) → (n+x<′k : n + x <′ k) → (x<′k : x <′ k) →
  plus-mod! k n x x<′k ≡ n + x
plus-mod-lt! k zero x n+x<′k x<′k = refl
plus-mod-lt! .(suc x) (suc n) x n+x<′k ≤′-refl
  = ⊥-elim (helper n x (≤′-pred n+x<′k))
  where
    helper : ∀ n x → suc (n + x) ≤′ x → ⊥
    helper zero zero ()
    helper zero (suc x) h = helper zero x (≤′-pred h)
    helper (suc n) x h = helper n x (≤′-pred (≤′-step h))
plus-mod-lt! .(suc k') (suc n) x n+x<′k (≤′-step {k'} x<′k′)
  rewrite sym (+s n x)
  = plus-mod-lt! (suc k') n (suc x) n+x<′k (s≤′s x<′k′)

plus-mod-lt : (k n x : ℕ) → (n+x<′k : n + x <′ k) →
  plus-mod! k n x (n+x<′k⇒x<′k n n+x<′k) ≡ n + x
plus-mod-lt k n x n+x<′k =
  plus-mod-lt! k n x n+x<′k (n+x<′k⇒x<′k n n+x<′k)

-- To be continued...
