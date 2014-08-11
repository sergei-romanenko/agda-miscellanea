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
  using (Bool; true; false; _≟_; not)
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
  later : ∀ {ws} → (l : ∀ w → Bar (w ∷ ws)) → Bar ws


-- auxiliaries

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

≢-trans : ∀ {x y z : Letter} →
            x ≢ y → y ≢ z → x ≡ z
≢-trans  {x} {y} {z} x≢y y≢z = begin
  x ≡⟨ ¬-not x≢y ⟩ not y ≡⟨ sym (¬-not (≢-sym y≢z)) ⟩ z ∎
  where open ≡-Reasoning


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

  prop2 : ∀ {zs a b xs ys} → a ≢ b → Bar xs → Bar ys →
            T a xs zs → T b ys zs → Bar zs

  prop2 a≢b (now gx) by ta tb = now (lemma3 ta gx)
  prop2 a≢b (later lx) by ta tb = prop2x a≢b lx by ta tb

  prop2x : ∀ {zs a b xs ys} → a ≢ b → (∀ w → Bar (w ∷ xs)) → Bar ys →
             T a xs zs → T b ys zs → Bar zs

  prop2x a≢b lx (now gy) ta tb = now (lemma3 tb gy)
  prop2x a≢b lx (later ly) ta tb = later (prop2y a≢b lx ly ta tb)

  prop2y : ∀ {zs a b xs ys} → a ≢ b →
             (∀ w → Bar (w ∷ xs)) → (∀ w → Bar (w ∷ ys)) →
             T a xs zs → T b ys zs → (∀ w → Bar (w ∷ zs))

  prop2y {zs} a≢b lx ly ta tb [] = prop1 zs
  prop2y {zs} {a} {b} {xs} {ys} a≢b lx ly ta tb (c ∷ cs) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    prop2 a≢b (lx cs) (later ly)
          (T a (cs ∷ xs) ((a ∷ cs) ∷ zs) ∋ t-keep ta)
          (T b ys ((a ∷ cs) ∷ zs)        ∋ t-drop (≢-sym a≢b) tb)
  ... | no  c≢a rewrite (c ≡ b ∋ ≢-trans c≢a a≢b) =
    prop2x a≢b lx (ly cs)
           (T a xs ((b ∷ cs) ∷ zs)        ∋ t-drop a≢b ta)
           (T b (cs ∷ ys) ((b ∷ cs) ∷ zs) ∋ t-keep tb)


-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on xs ∈ bar, then induction on first word following zs

mutual

  prop3 : ∀ {a v ws} → Bar (v ∷ ws) → Bar (a ≪ (v ∷ ws))

  prop3 (now g) = now (lemma2 g)
  prop3 (later l) = later (prop3l l)

  prop3l : ∀ {a v ws} → (∀ w → Bar (w ∷ v ∷ ws)) → (∀ w → Bar (w ∷ a ≪ (v ∷ ws)))

  prop3l {a} {v} {ws} l [] =
    prop1 ((a ∷ v) ∷ a ≪ ws)
  prop3l {a} {v} {ws} l (c ∷ cs) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    prop3 (l cs)
  ... | no  c≢a =
    prop2 c≢a
          (Bar (cs ∷ a ≪ (v ∷ ws))
            ∋ prop3l l cs)
          (Bar (v ∷ ws)
            ∋ later l)
          (T c (cs ∷ a ≪ (v ∷ ws)) ((c ∷ cs) ∷ a ≪ (v ∷ ws))
            ∋ t-init c≢a)
          (T a (v ∷ ws) ((c ∷ cs) ∷ a ≪ (v ∷ ws))
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
