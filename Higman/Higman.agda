{-
    Title:      Higman.Agda
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004. 

    from Isabelle to Agda.
-}

module Higman where

open import Data.Nat
open import Data.Bool
  renaming (T to T′; _≟_ to _≟B_)
open import Data.Bool.Properties
  using (¬-not)
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  renaming([_] to [_]ⁱ)

Letter : Set
Letter = Bool

Word = List Letter

infix 4 _⊴_

data _⊴_ : Word → Word → Set where
  ⊴-[]   : ∀ {ys} → [] ⊴ ys
  ⊴-drop : ∀ {xs ys y} → xs ⊴ ys → xs ⊴ y ∷ ys
  ⊴-keep : ∀ {xs ys x} → xs ⊴ ys → x ∷ xs ⊴ x ∷ ys

data L (v : Word) : List Word → Set where
  L0 : ∀ {w ws} → (e : w ⊴ v) → L v (w ∷ ws)
  L1 : ∀ {w ws} → (l : L v ws) → L v (w ∷ ws)

data good : List Word → Set where
  good0 : ∀ {ws w} → (l : L w ws) → good (w ∷ ws)
  good1 : ∀ {ws w} → (g : good ws) → good (w ∷ ws)

infix 6 _≪_

_≪_ : (a : Letter) → List Word → List Word
a ≪ [] = []
a ≪ (w ∷ ws) = (a ∷ w) ∷ a ≪ ws

data T (a : Letter) : List Word → List Word → Set where
  T0 : ∀ {w ws b} → (a≢b : a ≢ b) →
       T a (w ∷ (b ≪ ws)) ((a ∷ w) ∷ (b ≪ ws))
  T1 : ∀ {w ws zs} →
       (t : T a ws zs) → T a (w ∷ ws) ((a ∷ w) ∷ zs)
  T2 : ∀ {w ws zs b} → (a≢b : a ≢ b) →
       (t : T a ws zs) → T a ws ((b ∷ w) ∷ zs)

-- Note the subtle scope of ∀ w !

data bar : List Word → Set where
  bar1 : ∀ {ws} → (g : good ws) → bar ws
  bar2 : ∀ {ws} → (b : ∀ w → bar (w ∷ ws)) → bar ws

-- prop1

prop1 : ∀ (ws : List Word) → bar ([] ∷ ws)
prop1 ws = bar2 (λ w → bar1 (good0 (L0 ⊴-[])))

-- lemmas

lemma1 : ∀ {x xs ws} → L xs ws → L (x ∷ xs) ws
lemma1 (L0 e) = L0 (⊴-drop e)
lemma1 (L1 l) = L1 (lemma1 l)

lemma2' : ∀ {x xs ws} → L xs ws → L (x ∷ xs) (x ≪ ws)
lemma2' (L0 e) = L0 (⊴-keep e)
lemma2' (L1 l) = L1 (lemma2' l)

lemma2 : ∀ {a ws} → good ws → good (a ≪ ws)
lemma2 (good0 l) = good0 (lemma2' l)
lemma2 (good1 g) = good1 (lemma2 g)

lemma3' : ∀ {x xs vs ws} →
          T x vs ws → L xs vs → L (x ∷ xs) ws
lemma3' (T0 a≢b) (L0 e) = L0 (⊴-keep e)
lemma3' (T0 a≢b) (L1 l) = L1 (lemma1 l)
lemma3' (T1 t) (L0 e) = L0 (⊴-keep e)
lemma3' (T1 t) (L1 l) = L1 (lemma3' t l)
lemma3' (T2 a≢b t) l = L1 (lemma3' t l)

lemma3 : ∀ {a ws zs} → T a ws zs → good ws → good zs
lemma3 (T0 a≢b) (good0 l) = good0 (lemma1 l)
lemma3 (T0 a≢b) (good1 g) = good1 g
lemma3 (T1 t) (good0 l) = good0 (lemma3' t l)
lemma3 (T1 t) (good1 g) = good1 (lemma3 t g)
lemma3 (T2 a≢b t) g = good1 (lemma3 t g)

lemma4 : ∀ {a w ws} → T a (w ∷ ws) (a ≪ (w ∷ ws))
lemma4 {true} {w} {[]} = T0 {b = false} (λ ())
lemma4 {false} {w} {[]} = T0 {b = true} (λ ())
lemma4 {_}  {w} {x ∷ xs} = T1 lemma4

-- auxiliaries

≢xyz : ∀ {x y z : Letter} →
          x ≢ z → y ≢ z → x ≡ y
≢xyz {x} {y} {z} x≢z y≢z = begin
  x ≡⟨ ¬-not x≢z ⟩ not z ≡⟨ sym (¬-not y≢z) ⟩ y ∎
  where open ≡-Reasoning

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

-- prop2

mutual

  prop2 : ∀ {a b} → a ≢ b → ∀ {xs} → bar xs → ∀ {ys} → bar ys →
          ∀ {zs} →
          T a xs zs → T b ys zs → bar zs
  prop2 a≢b (bar1 gx)  ysb Ta Tb = bar1 (lemma3 Ta gx)
  prop2 a≢b (bar2 b2x) ysb Ta Tb = prop2I a≢b b2x ysb Ta Tb

  prop2I : ∀ {a b} → a ≢ b → ∀ {xs} →  (∀ w → bar (w ∷ xs)) →
           ∀ {ys} → bar ys → ∀ {zs} →
             T a xs zs → T b ys zs → bar zs
  prop2I a≢b b2x (bar1 gy) Ta Tb = bar1 (lemma3 Tb gy)
  prop2I {a} {b} a≢b {xs} b2x {ys} (bar2 b2y) {zs} Ta Tb = bar2 prop2Iw
    where
      prop2Iw : (w : Word) → bar (w ∷ zs)
      prop2Iw [] = prop1 zs
      prop2Iw (c ∷ cs) with c ≟B a
      prop2Iw (c ∷ cs) | yes c≡a rewrite c≡a =
        prop2 a≢b (b2x cs) (bar2 b2y)
              (T1 Ta             ∶ T a (cs ∷ xs) ((a ∷ cs) ∷ zs))
              (T2 (≢-sym a≢b) Tb ∶ T b ys ((a ∷ cs) ∷ zs))
      prop2Iw (c ∷ cs) | no c≢a =
        prop2I a≢b b2x (b2y cs) (T2 (≢-sym c≢a) Ta) T1Tb
        where
          T1Tb : T b (cs ∷ ys) ((c ∷ cs) ∷ zs)
          T1Tb = subst (λ z → T b (cs ∷ ys) ((z ∷ cs) ∷ zs))
                       (≢xyz (≢-sym a≢b) c≢a ∶ b ≡ c)
                       (T1 Tb ∶ T b (cs ∷ ys) ((b ∷ cs) ∷ zs))

-- prop3

prop3 : ∀ {a x xs} → bar (x ∷ xs) →
          bar (a ≪ (x ∷ xs))
prop3 (bar1 g) = bar1 (lemma2 g)
prop3 {a} {x} {xs} (bar2 b) = bar2 prop3w
  where
    prop3w : (w : Word) → bar (w ∷ a ≪ (x ∷ xs))
    prop3w [] = prop1 ((a ∷ x) ∷ a ≪ xs)
    prop3w (c ∷ cs) with c ≟B a
    ... | yes c≡a rewrite c≡a = prop3 (b cs)
    ... | no  c≢a =
      prop2
        c≢a
        (prop3w cs ∶ bar (cs ∷ (a ∷ x) ∷ a ≪ xs))
        (bar2 b ∶ bar (x ∷ xs))
        (T0 c≢a ∶ T c (cs ∷ (a ∷ x) ∷ a ≪ xs) ((c ∷ cs) ∷ (a ∷ x) ∷ a ≪ xs))
        (T2 (≢-sym c≢a) lemma4 ∶ T a (x ∷ xs) ((c ∷ cs) ∷ (a ∷ x) ∷ a ≪ xs))

--
-- higman
--

higman' :  ∀ w → bar (w ∷ [])
higman' [] = prop1 []
higman' (c ∷ cs) = prop3 (higman' cs)

higman : bar []
higman = bar2 higman'

--
-- good-prefix-lemma
--

data is-prefix {A : Set} (f : ℕ → A) : List A → Set where
  is-prefix-[] : is-prefix f []
  is-prefix-∷  : ∀ {xs : List A} →
        is-prefix f xs → is-prefix f (f (length xs) ∷ xs)

test-is-prefix : is-prefix suc (3 ∷ 2 ∷ 1 ∷ [])
test-is-prefix = is-prefix-∷ (is-prefix-∷ (is-prefix-∷ is-prefix-[]))

good-prefix-lemma :
  ∀ (f : ℕ → Word) ws →
    bar ws → is-prefix f ws →
    Σ (List Word) (λ vs → is-prefix f vs × good vs)
good-prefix-lemma f ws (bar1 g) p = ws , p , g
good-prefix-lemma f ws (bar2 b) p =
  let w = f (length ws) in
  good-prefix-lemma f (w ∷ ws) (b w) (is-prefix-∷ p)

good-prefix :
  ∀ (f : ℕ → Word) →
    ∃ λ ws → (is-prefix f ws × good ws)
good-prefix f = good-prefix-lemma f [] higman is-prefix-[]
