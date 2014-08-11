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
  using (ℕ; zero; suc)
open import Data.Bool
  using (Bool; _≟_; not)
open import Data.Bool.Properties
  using (¬-not; not-¬)
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  renaming([_] to ≡[_])

Letter : Set
Letter = Bool

Word = List Letter

infix 4 _⊴_

data _⊴_ : Word → Word → Set where
  ⊴-[]   : ∀ {ys} → [] ⊴ ys
  ⊴-drop : ∀ {xs ys y} → xs ⊴ ys → xs ⊴ y ∷ ys
  ⊴-keep : ∀ {xs ys x} → xs ⊴ ys → x ∷ xs ⊴ x ∷ ys

data _⊵*_ (v : Word) : List Word → Set where
  ⊵*-now   : ∀ {w ws} → (n : w ⊴ v) → v ⊵* (w ∷ ws)
  ⊵*-later : ∀ {w ws} → (l : v ⊵* ws) → v ⊵* (w ∷ ws)

data good : List Word → Set where
  good-now   : ∀ {ws w} → (n : w ⊵* ws) → good (w ∷ ws)
  good-later : ∀ {ws w} → (l : good ws) → good (w ∷ ws)

infix 6 _≪_

_≪_ : (a : Letter) → List Word → List Word
a ≪ [] = []
a ≪ (w ∷ ws) = (a ∷ w) ∷ a ≪ ws

data T (a : Letter) : List Word → List Word → Set where
  t-init : ∀ {v ws b} → (a≢b : a ≢ b) →
           T a (v ∷ (b ≪ ws)) ((a ∷ v) ∷ (b ≪ ws))
  t-keep : ∀ {v vs ws} →
           (t : T a vs ws) → T a (v ∷ vs) ((a ∷ v) ∷ ws)
  t-drop : ∀ {v vs ws b} → (a≢b : a ≢ b) →
           (t : T a vs ws) → T a vs ((b ∷ v) ∷ ws)

-- Note the subtle scope of ∀ w !

data Bar : List Word → Set where
  now   : ∀ {ws} → (g : good ws) → Bar ws
  later : ∀ {ws} → (b : ∀ w → Bar (w ∷ ws)) → Bar ws

-- auxiliaries

≢xyz : ∀ {x y z : Letter} →
          x ≢ z → y ≢ z → x ≡ y
≢xyz {x} {y} {z} x≢z y≢z = begin
  x ≡⟨ ¬-not x≢z ⟩ not z ≡⟨ sym (¬-not y≢z) ⟩ y ∎
  where open ≡-Reasoning

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

-- prop1 : Sequences “ending” with empty word (trivial)

prop1 : ∀ (ws : List Word) → Bar ([] ∷ ws)
prop1 ws = later (λ w → now (good-now (⊵*-now ⊴-[])))

-- lemmas

lemma1 : ∀ {a w ws} → w ⊵* ws → (a ∷ w) ⊵* ws
lemma1 (⊵*-now n) = ⊵*-now (⊴-drop n)
lemma1 (⊵*-later l) = ⊵*-later (lemma1 l)

lemma2' : ∀ {a w ws} → w ⊵* ws → (a ∷ w) ⊵* (a ≪ ws)
lemma2' (⊵*-now n) = ⊵*-now (⊴-keep n)
lemma2' (⊵*-later l) = ⊵*-later (lemma2' l)

lemma2 : ∀ {a ws} → good ws → good (a ≪ ws)
lemma2 (good-now n) = good-now (lemma2' n)
lemma2 (good-later l) = good-later (lemma2 l)

lemma3' : ∀ {a v vs ws} →
          T a vs ws → v ⊵* vs → (a ∷ v) ⊵* ws
lemma3' (t-init a≢b) (⊵*-now n) = ⊵*-now (⊴-keep n)
lemma3' (t-init a≢b) (⊵*-later l) = ⊵*-later (lemma1 l)
lemma3' (t-keep t) (⊵*-now n) = ⊵*-now (⊴-keep n)
lemma3' (t-keep t) (⊵*-later l) = ⊵*-later (lemma3' t l)
lemma3' (t-drop a≢b t) l = ⊵*-later (lemma3' t l)

lemma3 : ∀ {a vs ws} → T a vs ws → good vs → good ws
lemma3 (t-init a≢b) (good-now n) = good-now (lemma1 n)
lemma3 (t-init a≢b) (good-later l) = good-later l
lemma3 (t-keep t) (good-now n) = good-now (lemma3' t n)
lemma3 (t-keep t) (good-later l) = good-later (lemma3 t l)
lemma3 (t-drop a≢b t) g = good-later (lemma3 t g)

lemma4 : ∀ a v ws → T a (v ∷ ws) (a ≪ (v ∷ ws))
lemma4 a v [] = t-init (not-¬ refl)
lemma4 a v (w ∷ ws) = t-keep (lemma4 a w ws)

-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on xs ∈ bar and ys ∈ bar,
-- then case distinction on first letter of first word following zs

mutual

  prop2 : ∀ {a b} → a ≢ b → ∀ {xs} → Bar xs → ∀ {ys} → Bar ys →
          ∀ {zs} →
          T a xs zs → T b ys zs → Bar zs
  prop2 a≢b (now gx)  ysb ta tb = now (lemma3 ta gx)
  prop2 a≢b (later b2x) ysb ta tb = prop2I a≢b b2x ysb ta tb

  prop2I : ∀ {a b} → a ≢ b → ∀ {xs} →  (∀ w → Bar (w ∷ xs)) →
           ∀ {ys} → Bar ys → ∀ {zs} →
             T a xs zs → T b ys zs → Bar zs
  prop2I a≢b b2x (now gy) ta tb = now (lemma3 tb gy)
  prop2I {a} {b} a≢b {xs} b2x {ys} (later b2y) {zs} ta tb = later prop2Iw
    where
      prop2Iw : (w : Word) → Bar (w ∷ zs)
      prop2Iw [] = prop1 zs
      prop2Iw (c ∷ cs) with c ≟ a
      prop2Iw (c ∷ cs) | yes c≡a rewrite c≡a =
        prop2 a≢b (b2x cs) (later b2y)
              (T a (cs ∷ xs) ((a ∷ cs) ∷ zs)  ∋ t-keep ta)
              (T b ys ((a ∷ cs) ∷ zs)         ∋ t-drop (≢-sym a≢b) tb)
      prop2Iw (c ∷ cs) | no c≢a rewrite (c ≡ b ∋ ≢xyz c≢a (≢-sym a≢b)) =
        prop2I a≢b b2x (b2y cs)
               (T a xs ((b ∷ cs) ∷ zs)         ∋ t-drop a≢b ta)
               (T b (cs ∷ ys) ((b ∷ cs) ∷ zs)  ∋ t-keep tb)

-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on xs ∈ bar, then induction on first word following zs

prop3 : ∀ {a v ws} → Bar (v ∷ ws) →
          Bar (a ≪ (v ∷ ws))
prop3 (now g) = now (lemma2 g)
prop3 {a} {v} {ws} (later b) = later prop3w
  where
    prop3w : (w : Word) → Bar (w ∷ a ≪ (v ∷ ws))
    prop3w [] = prop1 ((a ∷ v) ∷ a ≪ ws)
    prop3w (c ∷ cs) with c ≟ a
    ... | yes c≡a rewrite c≡a = prop3 (b cs)
    ... | no  c≢a =
      prop2
        c≢a
        (Bar (cs ∷ (a ∷ v) ∷ a ≪ ws) ∋ prop3w cs)
        (Bar (v ∷ ws)                 ∋ later b)
        (T c (cs ∷ (a ∷ v) ∷ a ≪ ws) ((c ∷ cs) ∷ (a ∷ v) ∷ a ≪ ws)
          ∋ t-init c≢a)
        (T a (v ∷ ws) ((c ∷ cs) ∷ (a ∷ v) ∷ a ≪ ws)
          ∋ t-drop (≢-sym c≢a) (lemma4 a v ws))

--
-- higman: Main theorem
--

higman' :  ∀ w → Bar (w ∷ [])
higman' [] = prop1 []
higman' (c ∷ cs) = prop3 (higman' cs)

higman : Bar []
higman = later higman'

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
    Bar ws → is-prefix f ws →
    ∃ λ (vs : List Word) → is-prefix f vs × good vs
good-prefix-lemma f ws (now g) p = ws , p , g
good-prefix-lemma f ws (later b) p =
  let w = f (length ws) in
  good-prefix-lemma f (w ∷ ws) (b w) (is-prefix-∷ p)

-- Finding good prefixes of infinite sequences

good-prefix :
  ∀ (f : ℕ → Word) →
    ∃ λ ws → (is-prefix f ws × good ws)
good-prefix f = good-prefix-lemma f [] higman is-prefix-[]
