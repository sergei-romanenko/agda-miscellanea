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

open ≡-Reasoning

data Letter : Set where
  lA : Letter
  lB : Letter

Word = List Letter

~ : Letter → Letter
~ lA = lB
~ lB = lA

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
  T0 : ∀ {w ws zs} →
       R (~ a) ws zs → T a (w ∷ zs) ((a ∷ w) ∷ zs)
  T1 : ∀ {w ws zs} →
       T a ws zs → T a (w ∷ ws) ((a ∷ w) ∷ zs)
  T2 : ∀ {w ws zs} →
       T a ws zs → T a ws (((~ a) ∷ w) ∷ zs)

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

lemma3' : ∀ {vs ws xs} x →
          T x vs ws → L xs vs → L (x ∷ xs) ws
lemma3' _ (T0 r) (L0 e) = L0 (⊴-keep e)
lemma3' _ (T0 r) (L1 l) = L1 (lemma1 l)
lemma3' _ (T1 t) (L0 e) = L0 (⊴-keep e)
lemma3' lA (T1 t) (L1 l) = L1 (lemma3' lA t l)
lemma3' lA (T2 t) l = L1 (lemma3' lA t l)
lemma3' lB (T1 t) (L1 l) = L1 (lemma3' lB t l)
lemma3' lB (T2 t) l = L1 (lemma3' lB t l)

lemma3 : ∀ {ws zs a} →
         T a ws zs → good ws → good zs
lemma3 (T0 r) (good0 l) = good0 (lemma1 l)
lemma3 (T0 r) (good1 g) = good1 g
lemma3 (T1 t) (good0 l) = good0 (lemma3' _ t l)
lemma3 (T1 t) (good1 g) = good1 (lemma3 t g)
lemma3 (T2 t) g = good1 (lemma3 t g)

lemma4 : ∀ {ws zs w} → {a : Letter} →
          R a (w ∷ ws) zs → T a (w ∷ ws) zs
lemma4 (R1 R0) = T0 R0
lemma4 (R1 (R1 r)) = T1 (lemma4 (R1 r))

{-
letter≢ : ∀ {a b c : Letter} →
             a ≢ b → c ≢ a → c ≡ b
letter≢ a≢b c≢a = {!-c!}
-}
{-
letter≢ {.lB} {lA} a≢b lA≢lB = refl
letter≢ {.lA} {lA} () lB≢lA
letter≢ {.lB} {lB} () lA≢lB
letter≢ {.lA} {lB} a≢b lB≢lA = refl
-}

_≟L_ : ∀ (a b : Letter) → Dec (a ≡ b)
--a ≟L b = {!!}
lA ≟L lA = yes refl
lA ≟L lB = no (λ ())
lB ≟L lA = no (λ ())
lB ≟L lB = yes refl

mutual

  prop2 : ∀ a → ∀ {xs} → bar xs → ∀ {ys} → bar ys → ∀ zs →
          T a xs zs → T (~ a) ys zs → bar zs
  prop2 lA xsb ysb zs Ta Tb = prop2I xsb ysb zs Ta Tb
  prop2 lB xsb ysb zs Ta Tb = prop2I ysb xsb zs Tb Ta

  prop2I : ∀ {xs} → bar xs → ∀ {ys} → bar ys → ∀ zs →
           T lA xs zs → T lB ys zs → bar zs
  prop2I (bar1 gx)  ysb zs Ta Tb = bar1 (lemma3 Ta gx)
  prop2I (bar2 b2x) ysb zs Ta Tb = prop2I' b2x ysb zs Ta Tb

  prop2I' : ∀ {xs} → (∀ w → bar (w ∷ xs)) → ∀ {ys} → bar ys → ∀ zs →
            T lA xs zs → T lB ys zs → bar zs
  prop2I' b2x (bar1 gy)  zs Ta Tb = bar1 (lemma3 Tb gy)
  prop2I' b2x (bar2 b2y) zs Ta Tb = bar2 prop2Iw
    where
      prop2Iw : (w : Word) → bar (w ∷ zs)
      prop2Iw [] = prop1 zs
      prop2Iw (lA ∷ cs) =
        prop2I  (b2x cs) (bar2 b2y)
                ((lA ∷ cs) ∷ zs) (T1 Ta) (T2 Tb)
      prop2Iw (lB ∷ cs) =
        prop2I' b2x (b2y cs)   
                ((lB ∷ cs) ∷ zs) (T2 Ta) (T1 Tb)

mutual

  prop3 : ∀ a x xs → bar (x ∷ xs) → ∀ zs →
            R a (x ∷ xs) zs → bar zs
  prop3 lA x xs xsb zs Ra = prop3Ia x xs xsb zs Ra
  prop3 lB x xs xsb zs Ra = prop3Ib x xs xsb zs Ra

  prop3Ia : ∀ x xs → bar (x ∷ xs) → ∀ zs →
             R lA (x ∷ xs) zs → bar zs
  prop3Ia x xs (bar1 g) zs Ra = bar1 (lemma2 Ra g)
  prop3Ia x xs (bar2 b2x) zs Ra = bar2 prop3Iaw
    where
      prop3Iaw : (w : Word) → bar (w ∷ zs)
      prop3Iaw [] = prop1 zs
      prop3Iaw (lA ∷ cs) =
        prop3Ia cs (x ∷ xs) (b2x cs) ((lA ∷ cs) ∷ zs) (R1 Ra)
      prop3Iaw (lB ∷ cs) =
        prop2 lB (prop3Iaw cs) (bar2 b2x) ((lB ∷ cs) ∷ zs)
              (T0 Ra) (T2 (lemma4 Ra))

  prop3Ib : ∀ x xs → bar (x ∷ xs) → ∀ zs →
             R lB (x ∷ xs) zs → bar zs
  prop3Ib x xs (bar1 g) zs Rb = bar1 (lemma2 Rb g)
  prop3Ib x xs (bar2 b2x) zs Rb = bar2 prop3Ibw
    where
      prop3Ibw : (w : Word) → bar (w ∷ zs)
      prop3Ibw [] = prop1 zs
      prop3Ibw (lB ∷ cs) =
        prop3Ib cs (x ∷ xs) (b2x cs) ((lB ∷ cs) ∷ zs) (R1 Rb)
      prop3Ibw (lA ∷ cs) =
        prop2 lA (prop3Ibw cs) (bar2 b2x) ((lA ∷ cs) ∷ zs)
              (T0 Rb) (T2 (lemma4 Rb))

higman' : ∀ w → bar (w ∷ [])
higman' [] = prop1 []
higman' (c ∷ cs) =
  prop3 c cs [] (higman' cs) ((c ∷ cs) ∷ []) (R1 R0)

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
    bar ws →
    is-prefix f ws →
    Σ (List Word) (λ vs → is-prefix f vs × good vs)
good-prefix-lemma f ws (bar1 g) p = ws , p , g
good-prefix-lemma f ws (bar2 b) p =
  let w = f (length ws) in
  good-prefix-lemma f (w ∷ ws) (b w) (is-prefix-∷ p)

good-prefix :
  ∀ (f : ℕ → Word) →
    ‌Σ (List Word) (λ vs → (is-prefix f vs × good vs))
good-prefix f = good-prefix-lemma f [] higman is-prefix-[]
