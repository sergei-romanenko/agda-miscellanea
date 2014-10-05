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

-- Words are modelled as lists of letters from
-- the two letter alphabet.

Letter : Set
Letter = Bool

Word = List Letter

-- The embedding relation on words is defined inductively.
-- Intuitively, a word xs can be embedded into a word ys,
-- if we can obtain xs by deleting letters from ys.
-- For example,
--   true ∷ true ∷ [] ⊴ false ∷ true ∷ false ∷ true ∷ []

infix 4 _⊴_ _⊵∃_

data _⊴_ : Word → Word → Set where
  ⊴-[]   : ∀ {ys} → [] ⊴ ys
  ⊴-drop : ∀ {xs ys y} → xs ⊴ ys → xs ⊴ y ∷ ys
  ⊴-keep : ∀ {xs ys x} → xs ⊴ ys → x ∷ xs ⊴ x ∷ ys

-- In order to formalize the notion of a good sequence,
-- it is useful to define an auxiliary relation _⊵∃_.
--   v ⊵∃ ws
-- means that ws contains a word w, such that w ⊴ v .

data _⊵∃_ (v : Word) : List Word → Set where
  ⊵∃-now   : ∀ {w ws} (n : w ⊴ v) → v ⊵∃ w ∷ ws
  ⊵∃-later : ∀ {w ws} (l : v ⊵∃ ws) → v ⊵∃ w ∷ ws

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

data Good : List Word → Set where
  good-now   : ∀ {ws w} (n : w ⊵∃ ws) → Good (w ∷ ws)
  good-later : ∀ {ws w} (l : Good ws) → Good (w ∷ ws)

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

data Bar : List Word → Set where
  now   : ∀ {ws} (g : Good ws) → Bar ws
  later : ∀ {ws} (l : ∀ w → Bar (w ∷ ws)) → Bar ws

-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)


-- The following function adds a letter to each word in a word list. 

infixr 5 _∷∈_

_∷∈_ : (a : Letter) (ws : List Word) → List Word
a ∷∈ [] = []
a ∷∈ (w ∷ ws) = (a ∷ w) ∷ a ∷∈ ws

-- `T a vs ws` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a ≢ b, and
-- (2) then appending the tails of words starting with a.

data T (a : Letter) : List Word → List Word → Set where
  t-init : ∀ {v ws b} → (a≢b : a ≢ b) →
           T a (v ∷ b ∷∈ ws) ((a ∷ v) ∷ b ∷∈ ws)
  t-keep : ∀ {v vs ws} →
           (t : T a vs ws) → T a (v ∷ vs) ((a ∷ v) ∷ ws)
  t-drop : ∀ {v vs ws b} → (a≢b : a ≢ b) →
           (t : T a vs ws) → T a vs ((b ∷ v) ∷ ws)

-- Auxiliaries

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

≢-trans : ∀ {x y z : Letter} →
            x ≢ y → y ≢ z → x ≡ z
≢-trans  {x} {y} {z} x≢y y≢z = begin
  x ≡⟨ ¬-not x≢y ⟩ not y ≡⟨ sym (¬-not (≢-sym y≢z)) ⟩ z ∎
  where open ≡-Reasoning

--
-- The proof of Higman’s lemma is divided into several parts, namely
-- prop1, prop2 and prop3.
-- From the computational point of view, these theorems can be thought of
-- as functions transforming trees.

--
-- prop1 : Sequences “ending” with empty word (trivial)
-- A sequence ending with the empty word satisfies predicate Bar,
-- since it can trivially be extended to a good sequence
-- by appending any word.
--

bar[]∷ : (ws : List Word) → Bar ([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (⊵∃-now ⊴-[])))


-- Lemmas. w ⊵∃ ... → (a ∷ w) ⊵∃ ...

∷⊵∃ : ∀ {a w ws} → w ⊵∃ ws → a ∷ w ⊵∃ ws
∷⊵∃ (⊵∃-now n) = ⊵∃-now (⊴-drop n)
∷⊵∃ (⊵∃-later l) = ⊵∃-later (∷⊵∃ l)

∷⊵∃∷ : ∀ {a w ws} → w ⊵∃ ws → a ∷ w ⊵∃ a ∷∈ ws
∷⊵∃∷ (⊵∃-now n) = ⊵∃-now (⊴-keep n)
∷⊵∃∷ (⊵∃-later l) = ⊵∃-later (∷⊵∃∷ l)

t∷⊵∃ : ∀ {a v vs ws} → T a vs ws → v ⊵∃ vs → a ∷ v ⊵∃ ws
t∷⊵∃ (t-init a≢b) (⊵∃-now n) = ⊵∃-now (⊴-keep n)
t∷⊵∃ (t-init a≢b) (⊵∃-later l) = ⊵∃-later (∷⊵∃ l)
t∷⊵∃ (t-keep t) (⊵∃-now n) = ⊵∃-now (⊴-keep n)
t∷⊵∃ (t-keep t) (⊵∃-later l) = ⊵∃-later (t∷⊵∃ t l)
t∷⊵∃ (t-drop a≢b t) l = ⊵∃-later (t∷⊵∃ t l)

-- Lemmas. Good ... → Good ...

good∷∈ : ∀ {a ws} → Good ws → Good (a ∷∈ ws)
good∷∈ (good-now n) = good-now (∷⊵∃∷ n)
good∷∈ (good-later l) = good-later (good∷∈ l)

tGood : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
tGood (t-init a≢b) (good-now n) = good-now (∷⊵∃ n)
tGood (t-init a≢b) (good-later l) = good-later l
tGood (t-keep t) (good-now n) = good-now (t∷⊵∃ t n)
tGood (t-keep t) (good-later l) = good-later (tGood t l)
tGood (t-drop a≢b t) g = good-later (tGood t g)

-- Lemma. T a (...) (a ∷∈ ...)

t∷∈ : ∀ a ws → ws ≢ [] → T a ws (a ∷∈ ws)
t∷∈ a [] ws≢[] = ⊥-elim (ws≢[] refl)
t∷∈ a (v ∷ []) ws≢[] = t-init (not-¬ refl)
t∷∈ a (v ∷ w ∷ ws) ws≢[] = t-keep (t∷∈ a (w ∷ ws) (λ ()))

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
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
  ttBar₂ {zs} {a} {b} {xs} {ys} a≢b ta tb lx ly (c ∷ v) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    Bar ((a ∷ v) ∷ zs) ∋
    ttBar a≢b
          (T a (v ∷ xs) ((a ∷ v) ∷ zs)
            ∋ t-keep ta)
          (T b ys ((a ∷ v) ∷ zs)
            ∋ t-drop (≢-sym a≢b) tb)
          ({- Bar (v ∷ xs)
            ∋ -} lx v)
          (Bar ys
            ∋ later ly)
  ... | no  c≢a rewrite c ≡ b ∋ ≢-trans c≢a a≢b =
    Bar ((b ∷ v) ∷ zs) ∋
    ttBar₁ a≢b
           (T a xs ((b ∷ v) ∷ zs)
             ∋ t-drop a≢b ta)
           (T b (v ∷ ys) ((b ∷ v) ∷ zs)
             ∋ t-keep tb)
           ({- (∀ w → Bar (w ∷ xs))
             ∋ -} lx)
           ({- Bar (v ∷ ys)
             ∋ -} ly v)


--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar xs, then induction on first word following zs

mutual

  bar∷∈ : ∀ {a ws} → ws ≢ [] → Bar ws → Bar (a ∷∈ ws)

  bar∷∈ ws≢[] (now g) = now (good∷∈ g)
  bar∷∈ ws≢[] (later l) = later (bar∷∈₁ ws≢[] l)

  bar∷∈₁ : ∀ {a ws} → ws ≢ [] →
             (∀ w → Bar (w ∷ ws)) → (∀ w → Bar (w ∷ a ∷∈ ws))

  bar∷∈₁ {a} {ws} ws≢[] l [] = bar[]∷ (a ∷∈ ws)
  bar∷∈₁ {a} {ws} ws≢[] l (b ∷ v) with b ≟ a
  ... | yes b≡a rewrite b≡a =
    Bar (a ∷∈ (v ∷ ws)) ∋
    bar∷∈ (λ ()) (l v)
  ... | no  b≢a =
    Bar ((b ∷ v) ∷ a ∷∈ ws) ∋
    ttBar b≢a
          (T b (v ∷ a ∷∈ ws) ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-init b≢a)
          (T a ws ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-drop (≢-sym b≢a) (t∷∈ a ws ws≢[]))
          (Bar (v ∷ a ∷∈ ws)
            ∋ bar∷∈₁ ws≢[] l v)
          (Bar ws
            ∋ later l)


--
-- higman: Main theorem
--

higman′ :  ∀ w → Bar (w ∷ [])
higman′ [] = bar[]∷ []
higman′ (c ∷ cs) = bar∷∈ (λ ()) (higman′ cs)

higman : Bar []
higman = later higman′


--
-- good-prefix-lemma
--

data Is-prefix {A : Set} (f : ℕ → A) : List A → Set where
  zero : Is-prefix f []
  suc  : ∀ {xs : List A} →
        Is-prefix f xs → Is-prefix f (f (length xs) ∷ xs)

test-is-prefix : Is-prefix (λ k → suc (suc k)) (4 ∷ 3 ∷ 2 ∷ [])
test-is-prefix = suc (suc (suc zero))

good-prefix-lemma :
  ∀ (f : ℕ → Word) ws →
    Bar ws → Is-prefix f ws →
    ∃ λ vs → Is-prefix f vs × Good vs
good-prefix-lemma f ws (now g) p =
  ws , p , g
good-prefix-lemma f ws (later l) p =
  let w = f (length ws)
  in good-prefix-lemma f (w ∷ ws) (l w) (suc p)

-- Finding good prefixes of infinite sequences

good-prefix :
  ∀ (f : ℕ → Word) →
    ∃ λ ws → (Is-prefix f ws × Good ws)
good-prefix f = good-prefix-lemma f [] higman zero
