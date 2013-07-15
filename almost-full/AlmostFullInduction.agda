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
import Data.Fin

open import Data.Nat.Properties
import Algebra
private
  module CS =
    Algebra.CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open import Relation.Nullary
open import Relation.Unary
  hiding (Decidable)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function
import Function.Related

open import Induction.WellFounded

import Level

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

plus-mod : (k n x : ℕ) → ℕ
plus-mod k zero x = x
plus-mod k (suc n) x with k ≤? suc x
... | yes k≤sx = plus-mod k n zero
... | no  k≰sx = plus-mod k n (suc x)

-- Interesting lemmas about addition modulo k

-- plus-mod-<

plus-mod-< : (k n x : ℕ) →
  (x<k : x < k) → plus-mod k n x < k
plus-mod-< k zero x x<k = x<k
plus-mod-< k (suc n) x x<k with k ≤? suc x
... | yes k≤sx  = plus-mod-< k n zero 1≤k
  where open ≤-Reasoning
        1≤k = begin 1 ≤⟨ s≤s z≤n ⟩ suc x ≤⟨ x<k ⟩ k ∎
... | no  k≰sx  = plus-mod-< k n (suc x) (≰⇒> k≰sx)

-- plus-mod-fin

plus-mod-fin : {k : ℕ} (n : ℕ) (x : Finite k) → Finite k
plus-mod-fin {k} n (fin-intro x x<k) =
  fin-intro (plus-mod k n x) (plus-mod-< k n x x<k)

-- Auxiliaries

≡-pred : {n m : ℕ} → suc n ≡ suc m → n ≡ m
≡-pred refl = refl

+0 : (m : ℕ) → m + zero ≡ m
+0 zero = refl
+0 (suc n) = cong suc (+0 n)

+s : (m n : ℕ) → m + suc n ≡ suc (m + n)
+s zero n = refl
+s (suc m) n = cong suc (+s m n)

≤′-pred : {m n : ℕ} → suc m ≤′ suc n → m ≤′ n
≤′-pred = ≤⇒≤′ ∘ ≤-pred ∘ ≤′⇒≤

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) with ≤-antisym m≤n n≤m
... | refl = refl

-- plus-mod-lt

plus-mod-lt : (k n x : ℕ) → (n+x<k : n + x < k) →
  plus-mod k n x ≡ n + x
plus-mod-lt k zero x n+x<k = refl
plus-mod-lt k (suc n) x n+x<k with k ≤? suc x
... | yes k≤sx = ⊥-elim (<-asym n+x<k k≤snx)
  where
    open ≤-Reasoning
    k≤snx = begin k ≤⟨ k≤sx ⟩ suc x ≤⟨ s≤s (n≤m+n n x) ⟩ suc (n + x) ∎
... | no  k≰sx rewrite sym (+s n x) = plus-mod-lt k n (suc x) n+x<k

-- plus-mod-0

plus-mod-0 : (k n : ℕ) → n < k →
  plus-mod k n zero ≡ n
plus-mod-0 k n n<k  =
  subst (λ e → plus-mod k n 0 ≡ e) (+0 n) (plus-mod-lt k n 0 n+0<k)
  where 
    n+0<k : n + 0 < k
    n+0<k = subst (flip _<_ k) (sym (+0 n)) n<k

-- plus-mod-gt

plus-mod-gt! : (k n x : ℕ) → 0 < k → n < k → x < k →
  k ≤ n + x → plus-mod k n x + k ≡ (n + x)
plus-mod-gt! k zero x 0<k n<k x<k k≤n+x =
  ⊥-elim (<-asym (s≤s k≤n+x) x<k)
plus-mod-gt! k (suc n) x 0<k n<k x<k k≤n+x with k ≤? suc x
... | yes k≤sx = helper
  where
    open ≤-Reasoning
    n′<k : suc n ≤ k
    n′<k = begin suc n ≤⟨ n≤m+n 1 (suc n) ⟩ suc (suc n) ≤⟨ n<k ⟩ k ∎
    k≡sx : k ≡ suc x
    k≡sx = ≤-antisym k≤sx x<k
    helper : plus-mod k n 0 + k ≡ suc (n + x)
    helper rewrite plus-mod-0 k n n′<k | sym (+s n x) | k≡sx = refl
... | no  k≰sx rewrite sym (+s n x) =
  plus-mod-gt! k n (suc x) 0<k n′<k (≰⇒> k≰sx) k≤n+x
    where
      open ≤-Reasoning
      n′<k = begin suc n ≤⟨ n≤m+n 1 (suc n) ⟩ suc (suc n) ≤⟨ n<k ⟩ k ∎

plus-mod-gt : (k n x : ℕ) → 0 < k → n < k → (x<k : x < k) →
  k ≤ n + x → plus-mod k n x ≡ (n + x) ∸ k
plus-mod-gt k n x 0<k n<k x<k k≤n+x =
  begin
    plus-mod k n x
      ≡⟨ sym (m+n∸n≡m (plus-mod k n x) k) ⟩
    plus-mod k n x + k ∸ k
      ≡⟨ cong (flip _∸_ k) (plus-mod-gt! k n x 0<k n<k x<k k≤n+x) ⟩
    n + x ∸ k
  ∎
  where open ≡-Reasoning

-- plus-mod-diff

plus-mod-diff : ∀ k n x → 1 < k → 0 < n → n < k → x < k →
  x ≡ plus-mod k n x → ⊥
plus-mod-diff k n x 1<k 0<n n<k x<k x≡pm with k ≤? (n + x)
... | yes k≤n+x = get⊥
  where
    1≤k : 1 ≤ k
    1≤k = begin 1 ≤⟨ s≤s z≤n ⟩ 2 ≤⟨ 1<k ⟩ k ∎
      where open ≤-Reasoning

    x+k≡x+n : x + k ≡ x + n
    x+k≡x+n =
      begin
        x + k
          ≡⟨ cong (flip _+_ k) x≡pm ⟩
        plus-mod k n x + k
          ≡⟨ cong (flip _+_ k) (plus-mod-gt k n x 1≤k n<k x<k k≤n+x) ⟩
        (n + x ∸ k) + k
          ≡⟨ CS.+-comm (n + x ∸ k) k ⟩
        k + ((n + x) ∸ k)
          ≡⟨ m+n∸m≡n {k}{n + x} k≤n+x ⟩
        n + x
          ≡⟨ CS.+-comm n x ⟩
        x + n
      ∎
      where open ≡-Reasoning

    x+n<x+k : ∀ x → x + n < x + k
    x+n<x+k zero = n<k
    x+n<x+k (suc x) = s≤s (x+n<x+k x)

    get⊥ : ⊥
    get⊥ = 1+n≰n (subst (λ l → x + n < l) x+k≡x+n (x+n<x+k x))

... | no  k≰n+x = x≢x+n 0<n x≡x+n
  where
    x≡x+n : x ≡ x + n
    x≡x+n =
      begin
        x
          ≡⟨ x≡pm ⟩
        plus-mod k n x
          ≡⟨ plus-mod-lt k n x (≰⇒> k≰n+x) ⟩
        n + x
          ≡⟨ CS.+-comm n x ⟩
        x + n
      ∎
      where open ≡-Reasoning

    x≢x+n : ∀ {n} → 0 < n → x ≢ x + n
    x≢x+n {.(suc n)} (s≤s {.0} {n} _) x≡x+n rewrite +s x n = m≢1+m+n x x≡x+n

-- plus-mod-wraparound

plus-mod-wraparound : (n m x : ℕ) → x < m → 0 < n → 
     plus-mod (n + m) m (n + x) ≡ x
plus-mod-wraparound n zero x () 0<n
plus-mod-wraparound n (suc m) x sx≤sm 0<n with (n + suc m) ≤? suc (n + x)
... | yes sn+m≤sn+x rewrite +s n m =
  begin
    plus-mod (suc (n + m)) m zero
      ≡⟨ plus-mod-0 (suc (n + m)) m (s≤s (n≤m+n n m)) ⟩
    m
      ≡⟨ ≤-antisym (cancel-+-left-≤ (suc n) sn+m≤sn+x) (≤-pred sx≤sm) ⟩
    x
  ∎
  where open ≡-Reasoning

... | no sn+m≰sn+x rewrite +s n m =
  plus-mod-wraparound (suc n) m x x<m (s≤s z≤n)
  where
    prop₁ : suc (n + x) ≤ n + m
    prop₁ = ≤-pred (≰⇒> sn+m≰sn+x)
    prop₂ : n + suc x ≤ n + m
    prop₂ = subst (flip _≤_ (n + m)) (sym (+s n x)) prop₁
    x<m : suc x ≤ m
    x<m = cancel-+-left-≤ n prop₂


plus-mod-suc : ∀ m x → x < m → 
  plus-mod (suc m) m (suc x) ≡ x
plus-mod-suc zero x ()
plus-mod-suc (suc m) x x<sm with m ≤? x
... | yes m≤x =
  begin
    plus-mod (suc (suc m)) m zero
      ≡⟨ plus-mod-0 (suc (suc m)) m (n≤1+n (suc m)) ⟩
    m
      ≡⟨ ≤-antisym m≤x (≤-pred x<sm) ⟩
    x
  ∎
  where open ≡-Reasoning
... | no  m≰x =
  plus-mod-wraparound 2 m x (≰⇒> m≰x) (s≤s z≤n)


