{-
    Title:      AlmostFull.Agda
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

module AlmostFull where

open import Data.Nat
open import Data.Product
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′ )
  renaming (map to map⊎)
open import Data.Empty
open import Data.Star
open import Data.Plus

open import Data.Nat.Properties
  using (≤⇒≤′; ≤′⇒≤)

open import Relation.Nullary
open import Relation.Unary
  hiding (Decidable)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function

open import Induction.WellFounded

import Level

open ≡-Reasoning

--
--  Basic setup, and almost-full relations
--

data Almost-full {ℓ} {X : Set ℓ} : Rel X ℓ → Set (Level.suc ℓ) where
  af-zt  : ∀ {R} → (r : ∀ x y → R x y) →
               Almost-full R
  af-sup : ∀ {R} → (s : ∀ u → Almost-full (λ x y → R x y ⊎ R u x)) →
               Almost-full R

af-⇒ : 
  ∀ {ℓ} {X : Set ℓ} {A : Rel X ℓ} → Almost-full A → 
  ∀ {B : Rel X ℓ} → (∀ x y → A x y → B x y) → Almost-full B
af-⇒ (af-zt r) AB =
  af-zt (λ x y → AB x y (r x y))
af-⇒ (af-sup s) AB = af-sup (λ u →
  af-⇒ (s u) (λ x y → map⊎ (AB x y) (AB u x)))

-- SecureBy implies that every infinite chain has two related elements

private

  s≤′ : ∀ {m n} → suc m ≤′ n → m ≤′ n
  s≤′ sm≤′n = ≤⇒≤′ (≤-pred (≤′⇒≤ (≤′-step sm≤′n)))

sec-binary-infinite-chain : 
    ∀ {ℓ} {X : Set ℓ} {R} (f : ℕ → X) → Almost-full R → 
    ∀ (k : ℕ) →
    ∃ λ m → ∃ λ n → (k ≤′ m) × (m <′ n) × R (f m) (f n)
sec-binary-infinite-chain f (af-zt {R'} r) k =
  k , (suc k) , ≤′-refl , ≤′-refl , (r (f k) (f (suc k)) ∶ R' (f k) (f (suc k)))
sec-binary-infinite-chain {R} f (af-sup {R'} s) k
  with sec-binary-infinite-chain f (s (f k)) (suc k)
... | m , n , sk≤′m , m<′n , inj₁ r =
  m , n , s≤′ sk≤′m , m<′n , (r ∶ R' (f m) (f n))
... | m , n , k≤′m  , m<′n , inj₂ r =
  k , m , ≤′-refl  , k≤′m , (r ∶ R' (f k) (f m))

af-inf-chain : ∀ {ℓ} {X : Set ℓ} {R} → Almost-full R → ∀ (f : ℕ → X) →
  ∃ λ m → ∃ λ n → (m <′ n) × R (f m) (f n)
af-inf-chain {R = R} afr f with sec-binary-infinite-chain f afr 0
... | m , n , 0≤′m , m<′n , r = m , n , m<′n , (r ∶ R (f m) (f n))

--
-- From a decidable Well-founded relation to an AlmostFull
--

-- Generalization to an arbitrary decidable well-founded relation

af-iter : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} 
         (decR : Decidable R) (z : X) (accX : Acc R z) →
         Almost-full (λ x y → ¬ (R x z) ⊎ ¬(R y x))

af-iter {R = R} d z (acc rs) = af-sup (λ u → help u (d u z))
  where
    help : ∀ u → Dec (R u z) →
      Almost-full (λ x y → (¬(R x z) ⊎ ¬(R y x)) ⊎ (¬(R u z) ⊎ ¬(R x u)))
    help u (yes Ruz) =
      af-⇒ (af-iter d u (rs u Ruz)) (λ _ _ → [ inj₂ ∘ inj₂ , inj₁ ∘ inj₂ ]′)
    help y (no ¬Ruz) = af-zt (λ _ _ → inj₂ (inj₁ ¬Ruz))

af-from-wf : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} →
  Well-founded R → Decidable R → Almost-full (λ x y → ¬ (R y x))
af-from-wf {X} {R} w d = af-sup (λ u →
  af-⇒ (af-iter d u (w u)) (λ _ _ → [ inj₂ , inj₁ ]′))

--
-- From an AlmostFull relation to a Well-Founded one
--

infixr 5 _◅ʳ_ _◅ʳ⁺_

_◅ʳ_ : ∀ {ℓ} {X : Set ℓ} {T : Rel X ℓ} {x z y} →
      Star T x y → T y z → Star T x z
ε ◅ʳ yz = yz ◅ ε
(x' ◅ xy) ◅ʳ yx = x' ◅ (xy ◅ʳ yx)

_◅ʳ⁺_ : ∀ {ℓ} {X : Set ℓ} {T : Rel X ℓ} →
      ∀ {x z y} → Star T x y → T y z → x [ T ]⁺ z
ε ◅ʳ⁺ yz = [ yz ]
(t ◅ xy) ◅ʳ⁺ yz =
  _ ∼⁺⟨ [ t ] ⟩ (xy ◅ʳ⁺ yz)

acc-from-af : 
  ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} →
  Almost-full R → (T : Rel X ℓ)→ ∀ x →
  (∀ z y → Star T y x → z [ T ]⁺ y → R y z → ⊥) → Acc T x
acc-from-af (af-zt r) T x h =
  acc (λ z t → ⊥-elim (h z x ε [ t ∶ T z x ] (r x z)))
acc-from-af {R = R} (af-sup s) T x h = acc (λ z tzx →
  acc-from-af (s x) T z
    (λ u y tyz t+uy →
      ([ h u y (tyz ◅ʳ tzx) t+uy , h y x ε (tyz ◅ʳ⁺ tzx) ]′
       ∶ (R y u ⊎ R x y → ⊥))))

wf-from-af : 
   ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} (T : Rel X ℓ) →
   (∀ x y → x [ T ]⁺ y → R y x → ⊥) → Almost-full R → Well-founded T
wf-from-af T h af y =
  acc-from-af af T y (λ x z _ → h x z)

--
-- A reassuring lemma
--

wf-from-wqo : 
  ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → Transitive R → Almost-full R → 
  Well-founded (λ x y → R x y × ¬(R y x))
wf-from-wqo {R = R} tr af =
  wf-from-af {R = R} (λ x y → R x y × ¬ R y x) get⊥ af
    where
      get~ : ∀ {x y} → Plus (λ x' y' → R x' y' × ¬ R y' x') x y → R x y
      get~ [ rxy , ¬ryx ] = rxy
      get~ (._ ∼⁺⟨ pxz ⟩ pzy) = tr (get~ pxz) (get~ pzy)

      get¬ : ∀ {x y} → Plus (λ x' y' → R x' y' × ¬ R y' x') x y →
                R y x → ∃ λ z → R y z × ¬ R y z
      get¬ [ rxy , ¬ryx ] ryx = _ , ryx , ¬ryx
      get¬ (._ ∼⁺⟨ pxz ⟩ pzy) ryx with get~ pxz
      ... | rxz with get¬ pzy (tr ryx rxz)
      ... | _ , ryz , ¬ryz = _ , ryz , ¬ryz

      get⊥ : ∀ x y → Plus (λ x' y' → R x' y' × ¬ R y' x') x y →
                R y x → ⊥
      get⊥ _ _ pxy ryx with get¬ pxy ryx
      get⊥ _ _ pxy ryx | _ , ryz , ¬ryz = ¬ryz ryz

--
-- 'Almost-full' ornamented with well-founded trees
--

data WFT {ℓ} (X  :  Set ℓ) : Set ℓ where 
  zt  : WFT X
  sup : (g : X → WFT X) → WFT X

data Almost-full# {ℓ} {X : Set ℓ} : Rel X ℓ → WFT X → Set (Level.suc ℓ) where
  af-zt#  : ∀ {R} → (r : ∀ x y → R x y) →
              Almost-full# R zt
  af-sup# : ∀ {R} →
              (g : X → WFT X)
              (s : ∀ u → Almost-full# (λ x y → R x y ⊎ R u x) (g u)) →
              Almost-full# R (sup g)

wft-from-af : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → Almost-full R → WFT X
wft-from-af (af-zt r) = zt
wft-from-af (af-sup s) = sup (λ u → wft-from-af (s u))

af⇒af# : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → (afR : Almost-full R) →
              Almost-full# R (wft-from-af afR)
af⇒af# (af-zt r) = af-zt# r
af⇒af# (af-sup s) =
  af-sup# (λ u → wft-from-af (s u)) (λ u → af⇒af# (s u))

af#⇒af : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} {t : WFT X} →
           Almost-full# R t → Almost-full R
af#⇒af (af-zt# r) = af-zt r
af#⇒af (af-sup# g s) = af-sup (λ u → af#⇒af (s u))

af#-⇒ : 
  ∀ {ℓ} {X : Set ℓ} {A : Rel X ℓ} (t : WFT X) → Almost-full# A t → 
  ∀ {B : Rel X ℓ} → (∀ x y → A x y → B x y) → Almost-full# B t
af#-⇒ zt (af-zt# r) AB = af-zt# (λ x y → AB x y (r x y))
af#-⇒ (sup g) (af-sup# .g s) AB =
  af-sup# g (λ u → af#-⇒ (g u) (s u) (λ x y → map⊎ (AB x y) (AB u x)))

--
-- Secure-by.
-- The tree can be separated from the relation.
--

Secure-by : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) (t :  WFT X) → Set ℓ
Secure-by R zt = ∀ x y → R x y
Secure-by R (sup g) = ∀ u → Secure-by (λ x y → R x y ⊎ R u x) (g u)

Almost-full! : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) → Set ℓ
Almost-full! {X = X} R = Σ (WFT X) (λ t → Secure-by R t)

af!⇒af : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → Almost-full! R → Almost-full R
af!⇒af (zt , srt) = af-zt srt
af!⇒af (sup g , srt) =
  af-sup (λ u → af!⇒af (g u , srt u))

af⇒af! : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → Almost-full R → Almost-full! R
af⇒af! (af-zt r) = zt , r
af⇒af! (af-sup s) =
  sup (λ u → proj₁ (af⇒af! (s u))) , (λ u → proj₂ (af⇒af! (s u)))

af⇒sec : ∀ {ℓ} {X : Set ℓ} {R : Rel X ℓ} → (afR : Almost-full R) →
           Secure-by R (wft-from-af afR)
af⇒sec (af-zt r) = r
af⇒sec (af-sup s) = λ u → af⇒sec (s u)

sec-⇒ :
  ∀ {ℓ} {X : Set ℓ} {A : Rel X ℓ} → (t : WFT X) → Secure-by A t → 
  ∀ {B : Rel X ℓ} → (∀ x y → A x y → B x y) → Secure-by B t
sec-⇒ zt secA a⇒b = λ x y → a⇒b x y (secA x y)
sec-⇒ (sup g) secA a⇒b =
  λ u → sec-⇒ (g u) (secA u) (λ x y → map⊎ (a⇒b x y) (a⇒b u x))

--
