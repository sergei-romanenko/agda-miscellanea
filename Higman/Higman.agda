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

data Good : List Word → Set where
  good-now   : ∀ {ws w} → (n : w ⊵* ws) → Good (w ∷ ws)
  good-later : ∀ {ws w} → (l : Good ws) → Good (w ∷ ws)

-- infixr 5 _∷_ _++_
infixr 6 _≪_

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
  now   : ∀ {ws} → (g : Good ws) → Bar ws
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

bar[]∷ : ∀ (ws : List Word) → Bar ([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (⊵*-now ⊴-[])))


-- lemmas

∷⊵* : ∀ {a w ws} → w ⊵* ws → (a ∷ w) ⊵* ws
∷⊵* (⊵*-now n) = ⊵*-now (⊴-drop n)
∷⊵* (⊵*-later l) = ⊵*-later (∷⊵* l)

∷⊵*≪ : ∀ {a w ws} → w ⊵* ws → (a ∷ w) ⊵* (a ≪ ws)
∷⊵*≪ (⊵*-now n) = ⊵*-now (⊴-keep n)
∷⊵*≪ (⊵*-later l) = ⊵*-later (∷⊵*≪ l)

good≪ : ∀ {a ws} → Good ws → Good (a ≪ ws)
good≪ (good-now n) = good-now (∷⊵*≪ n)
good≪ (good-later l) = good-later (good≪ l)

t∷⊵* : ∀ {a v vs ws} → T a vs ws → v ⊵* vs → (a ∷ v) ⊵* ws
t∷⊵* (t-init a≢b) (⊵*-now n) = ⊵*-now (⊴-keep n)
t∷⊵* (t-init a≢b) (⊵*-later l) = ⊵*-later (∷⊵* l)
t∷⊵* (t-keep t) (⊵*-now n) = ⊵*-now (⊴-keep n)
t∷⊵* (t-keep t) (⊵*-later l) = ⊵*-later (t∷⊵* t l)
t∷⊵* (t-drop a≢b t) l = ⊵*-later (t∷⊵* t l)

tGood : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
tGood (t-init a≢b) (good-now n) = good-now (∷⊵* n)
tGood (t-init a≢b) (good-later l) = good-later l
tGood (t-keep t) (good-now n) = good-now (t∷⊵* t n)
tGood (t-keep t) (good-later l) = good-later (tGood t l)
tGood (t-drop a≢b t) g = good-later (tGood t g)

t≪ : ∀ a ws → ws ≢ [] → T a ws (a ≪ ws)
t≪ a [] ws≢[] = ⊥-elim (ws≢[] refl)
t≪ a (v ∷ []) ws≢[] = t-init (a ≢ not a ∋ not-¬ refl)
t≪ a (v ∷ w ∷ ws) ws≢[] = t-keep (t≪ a (w ∷ ws) (w ∷ ws ≢ [] ∋ λ ()))

-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on xs ∈ bar and ys ∈ bar,
-- then case distinction on first letter of first word following zs

mutual

  ttBar : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
            Bar xs → Bar ys → Bar zs

  ttBar a≢b ta tb (now gx) by = now (tGood ta gx)
  ttBar a≢b ta tb (later lx) by = ttBar₁ a≢b ta tb lx by

  ttBar₁ : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → Bar ys → Bar zs

  ttBar₁ a≢b ta tb lx (now gy) = now (tGood tb gy)
  ttBar₁ a≢b ta tb lx (later ly) = later (ttBar₂ a≢b ta tb lx ly)

  ttBar₂ : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → (∀ w → Bar (w ∷ ys)) →
             (∀ w → Bar (w ∷ zs))

  ttBar₂ {zs} a≢b ta tb lx ly [] = bar[]∷ zs
  ttBar₂ {zs} {a} {b} {xs} {ys} a≢b ta tb lx ly (c ∷ cs) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    ttBar a≢b
          (T a (cs ∷ xs) ((a ∷ cs) ∷ zs) ∋ t-keep ta)
          (T b ys ((a ∷ cs) ∷ zs)        ∋ t-drop (≢-sym a≢b) tb)
          (lx cs) (later ly)
  ... | no  c≢a rewrite (c ≡ b ∋ ≢-trans c≢a a≢b) =
    ttBar₁ a≢b
           (T a xs ((b ∷ cs) ∷ zs)        ∋ t-drop a≢b ta)
           (T b (cs ∷ ys) ((b ∷ cs) ∷ zs) ∋ t-keep tb)
           lx (ly cs)


-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on xs ∈ bar, then induction on first word following zs

mutual

  bar≪ : ∀ {a ws} → ws ≢ [] → Bar ws → Bar (a ≪ ws)

  bar≪ w≢[] (now g) = now (good≪ g)
  bar≪ w≢[] (later l) = later (bar≪₁ w≢[] l)

  bar≪₁ : ∀ {a ws} → ws ≢ [] →
             (∀ w → Bar (w ∷ ws)) → (∀ w → Bar (w ∷ a ≪ ws))
  bar≪₁ {a} {ws} w≢[] l [] = bar[]∷ (a ≪ ws)
  bar≪₁ {a} {ws} w≢[] l (c ∷ cs) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    bar≪ (cs ∷ ws ≢ [] ∋ λ ()) (l cs)
  ... | no  c≢a =
    ttBar c≢a
          (T c (cs ∷ a ≪ ws) ((c ∷ cs) ∷ a ≪ ws)
            ∋ t-init c≢a)
          (T a ws ((c ∷ cs) ∷ a ≪ ws)
            ∋ t-drop (≢-sym c≢a) (t≪ a ws w≢[]))
          (Bar (cs ∷ a ≪ ws)
            ∋ bar≪₁ w≢[] l cs)
          (Bar ws
            ∋ later l)


--
-- higman: Main theorem
--

higman' :  ∀ w → Bar (w ∷ [])
higman' [] = bar[]∷ []
higman' (c ∷ cs) = bar≪ (cs ∷ [] ≢ [] ∋ λ ()) (higman' cs)

higman : Bar []
higman = later higman'


--
-- good-prefix-lemma
--

data Is-prefix {A : Set} (f : ℕ → A) : List A → Set where
  is-prefix-[] : Is-prefix f []
  is-prefix-∷  : ∀ {xs : List A} →
        Is-prefix f xs → Is-prefix f (f (length xs) ∷ xs)

test-is-prefix : Is-prefix suc (3 ∷ 2 ∷ 1 ∷ [])
test-is-prefix = is-prefix-∷ (is-prefix-∷ (is-prefix-∷ is-prefix-[]))

good-prefix-lemma :
  ∀ (f : ℕ → Word) ws →
    Bar ws → Is-prefix f ws →
    ∃ λ (vs : List Word) → Is-prefix f vs × Good vs
good-prefix-lemma f ws (now g) p = ws , p , g
good-prefix-lemma f ws (later b) p =
  let w = f (length ws) in
  good-prefix-lemma f (w ∷ ws) (b w) (is-prefix-∷ p)

-- Finding good prefixes of infinite sequences

good-prefix :
  ∀ (f : ℕ → Word) →
    ∃ λ ws → (Is-prefix f ws × Good ws)
good-prefix f = good-prefix-lemma f [] higman is-prefix-[]
