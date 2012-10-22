{- This program is free software; you can redistribute it and/or      -}
{- modify it under the terms of the GNU Lesser General Public License -}
{- as published by the Free Software Foundation; either version 2.1   -}
{- of the License, or (at your option) any later version.             -}
{-                                                                    -}
{- This program is distributed in the hope that it will be useful,    -}
{- but WITHOUT ANY WARRANTY; without even the implied warranty of     -}
{- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      -}
{- GNU General Public License for more details.                       -}
{-                                                                    -}
{- You should have received a copy of the GNU Lesser General Public   -}
{- License along with this program; if not, write to the Free         -}
{- Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA -}
{- 02110-1301 USA                                                     -}

module Higman where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming([_] to ≡[_])

open import Relation.Nullary.Decidable using (⌊_⌋)

--open ≡-Reasoning

data Letter : Set where
  lA : Letter
  lB : Letter

Word = List Letter

infix 4 _⊴_

data _⊴_ : Word → Word → Set where
  ⊴-[]   : ∀ {ys} → [] ⊴ ys
  ⊴-drop : ∀ {xs ys y} → xs ⊴ ys → xs ⊴ y ∷ ys
  ⊴-keep : ∀ {xs ys x} → xs ⊴ ys → x ∷ xs ⊴ x ∷ ys

data L (v : Word) : List Word → Set where
  L0 : ∀ {w ws} → w ⊴ v → L v (w ∷ ws)
  L1 : ∀ {w ws} → L v ws → L v (w ∷ ws)

data good : List Word → Set where
  good0 : ∀ {ws w} → L w ws → good (w ∷ ws)
  good1 : ∀ {ws w} → good ws → good (w ∷ ws)

data R (a : Letter) : List Word → List Word → Set where
  R0 : R a [] []
  R1 : ∀ {vs ws w} →
         R a vs ws → R a (w ∷ vs) ((a ∷ w) ∷ ws)

data T (a : Letter) : List Word → List Word → Set where
  T0 : ∀ {w ws zs b} → a ≢ b →
       R b ws zs → T a (w ∷ zs) ((a ∷ w) ∷ zs)
  T1 : ∀ {w ws zs} →
       T a ws zs → T a (w ∷ ws) ((a ∷ w) ∷ zs)
  T2 : ∀ {w ws zs b} → a ≢ b →
       T a ws zs → T a ws ((b ∷ w) ∷ zs)

-- Note the subtle scope of ∀ w !

data bar : List Word → Set where
  bar1 : ∀ {ws} → good ws → bar ws
  bar2 : ∀ {ws} → (∀ w → bar (w ∷ ws)) → bar ws

prop1 : ∀ (ws : List Word) → bar ([] ∷ ws)
prop1 ws = bar2 (λ w → bar1 (good0 (L0 ⊴-[])))

lemma1 : ∀ {ws x xs} → L xs ws → L (x ∷ xs) ws
lemma1 (L0 e) = L0 (⊴-drop e)
lemma1 (L1 l) = L1 (lemma1 l)

lemma2' : ∀ {vs ws x xs} →
          R x vs ws → L xs vs → L (x ∷ xs) ws
lemma2' R0 ()
lemma2' (R1 r) (L0 e) = L0 (⊴-keep e)
lemma2' (R1 r) (L1 l) = L1 (lemma2' r l)

lemma2 : ∀ {vs ws a} →
         R a vs ws → good vs → good ws
lemma2 R0 g = g
lemma2 (R1 r) (good0 l) = good0 (lemma2' r l)
lemma2 (R1 r) (good1 g) = good1 (lemma2 r g)

lemma3' : ∀ {vs ws xs x} →
          T x vs ws → L xs vs → L (x ∷ xs) ws
lemma3' (T0 ab r) (L0 e) = L0 (⊴-keep e)
lemma3' (T0 ab r) (L1 l) = L1 (lemma1 l)
lemma3' (T1 t) (L0 e) = L0 (⊴-keep e)
lemma3' (T1 t) (L1 l) = L1 (lemma3' t l)
lemma3' (T2 ab t) (L0 e) = L1 (lemma3' t (L0 e))
lemma3' (T2 ab t) (L1 l) = L1 (lemma3' t (L1 l))

lemma3 : ∀ {ws zs a} →
         T a ws zs → good ws → good zs
lemma3 (T0 ab r) (good0 l) = good0 (lemma1 l)
lemma3 (T0 ab r) (good1 g) = good1 g
lemma3 (T1 t) (good0 l) = good0 (lemma3' t l)
lemma3 (T1 t) (good1 g) = good1 (lemma3 t g)
lemma3 (T2 ab t) g = good1 (lemma3 t g)

lemma4 : ∀ {a w ws zs} →
          R a (w ∷ ws) zs → T a (w ∷ ws) zs
lemma4 {lA} (R1 R0) = T0 (λ ()) (R0 {lB})
lemma4 {lB} (R1 R0) = T0 (λ ()) (R0 {lA})
lemma4 (R1 (R1 r)) = T1 (lemma4 (R1 r))

≢abc : ∀ {a b c : Letter} →
             a ≢ b → c ≢ a → c ≡ b
≢abc {lA} {lA} {lB} a≢b c≢a = ⊥-elim (a≢b refl)
≢abc {lB} {lB} {lA} a≢b c≢a = ⊥-elim (a≢b refl)
≢abc {lA} {lB} {lA} a≢b c≢a = ⊥-elim (c≢a refl)
≢abc {lB} {lA} {lB} a≢b c≢a = ⊥-elim (c≢a refl)
≢abc {_}  {lA} {lA} a≢b c≢a = refl
≢abc {_}  {lB} {lB} a≢b c≢a = refl

_≟L_ : ∀ (a b : Letter) → Dec (a ≡ b)
--a ≟L b = {!!}
lA ≟L lA = yes refl
lA ≟L lB = no (λ ())
lB ≟L lA = no (λ ())
lB ≟L lB = yes refl

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
  prop2I {a} {b} a≢b b2x (bar2 b2y) {zs} Ta Tb = bar2 prop2Iw
    where
      prop2Iw : (w : Word) → bar (w ∷ zs)
      prop2Iw [] = prop1 zs
      prop2Iw (c ∷ cs) with c ≟L a
      prop2Iw (c ∷ cs) | yes c≡a rewrite c≡a =
        prop2 a≢b (b2x cs) (bar2 b2y)
                (T1 Ta) (T2 (λ b≡a → a≢b (sym b≡a)) Tb)
      prop2Iw (c ∷ cs) | no c≢a =
        prop2I a≢b b2x (b2y cs)
               (T2 (λ a≡c → c≢a (sym a≡c)) Ta)
               (subst (λ x → T b (cs ∷ _) ((x ∷ cs) ∷ zs))
                      (sym (≢abc a≢b c≢a)) (T1 Tb))


mutual

  prop3 : ∀ {a x xs} → bar (x ∷ xs) → ∀ {zs} →
            R a (x ∷ xs) zs → bar zs
  prop3 xsb Ra = prop3I xsb Ra

  prop3I : ∀ {a x xs} → bar (x ∷ xs) → ∀ {zs} →
             R a (x ∷ xs) zs → bar zs
  prop3I (bar1 g) Ra = bar1 (lemma2 Ra g)
  prop3I {a} (bar2 b2x) {zs} Ra = bar2 prop3Iw
    where
      prop3Iw : (w : Word) → bar (w ∷ zs)
      prop3Iw [] = prop1 zs
      prop3Iw (c ∷ cs) with c ≟L a
      prop3Iw (c ∷ cs) | yes c≡a rewrite c≡a =
        prop3I (b2x cs) (R1 Ra)
      prop3Iw (c ∷ cs) | no c≢a =
        prop2 c≢a (prop3Iw cs) (bar2 b2x)
              (T0 c≢a Ra) (T2 (λ a≡c → c≢a (sym a≡c)) (lemma4 Ra))

higman' :  ∀ w → bar (w ∷ [])
higman' [] = prop1 []
higman' (c ∷ cs) = prop3 (higman' cs) (R1 R0)

higman : bar []
higman = bar2 higman'

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
    ‌Σ (List Word) (λ vs → (is-prefix f vs × good vs))
good-prefix f = good-prefix-lemma f [] higman is-prefix-[]
