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

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming([_] to ≡[_])

open import Relation.Nullary.Decidable using (⌊_⌋)

open ≡-Reasoning

data Letter : Set where
  lA : Letter
  lB : Letter

Word = List Letter

data _≢L_ : (a b : Letter) → Set where
  lA≢lB : lA ≢L lB
  lB≢lA : lB ≢L lA

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
  T0 : ∀ {b w ws zs} →
       a ≢L b → R a ws zs → T a (w ∷ zs) ((a ∷ w) ∷ zs)
  T1 : ∀ {w ws zs} →
        T a ws zs → T a (w ∷ ws) ((a ∷ w) ∷ zs)
  T2 : ∀ {b w ws zs} →
       a ≢L b → T a ws zs → T a ws ((b ∷ w) ∷ zs)

data bar : List Word → Set where
  bar1 : ∀ {ws} → good ws → bar ws
  bar2 : ∀ {ws} w → bar (w ∷ ws) → bar ws

prop1 : ∀ (ws : List Word) → bar ([] ∷ ws)

prop1 ws = bar2 [] (bar1 (good0 (L0 ⊴-[])))

lemma1 : ∀ {ws xs x} → L xs ws → L (x ∷ xs) ws

lemma1 (L0 y) = L0 (⊴-drop y)
lemma1 (L1 y) = L1 (lemma1 y)

lemma2' : ∀ {vs ws x xs} →
          R x vs ws → L xs vs → L (x ∷ xs) ws
lemma2' R0 ()
lemma2' (R1 y) (L0 y') = L0 (⊴-keep y')
lemma2' (R1 y) (L1 y') = L1 (lemma2' y y')

lemma2 : ∀ {vs ws a} →
         R a vs ws → good vs → good ws
lemma2 R0 g = g
lemma2 (R1 y) (good0 y') = good0 (lemma2' y y')
lemma2 (R1 y) (good1 y') = good1 (lemma2 y y')

lemma3' : ∀ {vs ws x xs} →
          T x vs ws → L xs vs → L (x ∷ xs) ws
lemma3' (T0 y y') (L0 y0) = L0 (⊴-keep y0)
lemma3' (T0 y y') (L1 y0) = L1 (lemma1 y0)
lemma3' (T1 y) (L0 y') = L0 (⊴-keep y')
lemma3' (T1 y) (L1 y') = L1 (lemma3' y y')
lemma3' (T2 y y') l = L1 (lemma3' y' l)

lemma3 : ∀ {ws zs a} →
         T a ws zs → good ws → good zs
lemma3 (T0 y y') (good0 y0) = good0 (lemma1 y0)
lemma3 (T0 y y') (good1 y0) = good1 y0
lemma3 (T1 y) (good0 y') = good0 (lemma3' y y')
lemma3 (T1 y) (good1 y') = good1 (lemma3 y y')
lemma3 (T2 y y') g = good1 (lemma3 y' g)

lemma4 : ∀ {ws zs w} a →
          R a (w ∷ ws) zs → T a (w ∷ ws) zs
lemma4 lA (R1 R0) = T0 lA≢lB R0
lemma4 lA (R1 (R1 y)) = T1 (lemma4 lA (R1 y))
lemma4 lB (R1 R0) = T0 lB≢lA R0
lemma4 lB (R1 (R1 y)) = T1 (lemma4 lB (R1 y))

prop2 : ∀ {a b xs} →
        a ≢L b →
        bar xs →
        (ys : List Word) →
        bar ys →
        (zs : List Word) →
        T a xs zs → T b ys zs → bar zs
prop2 a≢b barxs ys barys zs Ta Tb = bar2 [] (prop1 zs)

prop3 : ∀ {a xs x} →
        bar (x ∷ xs) →
        (zs : List Word) →
        R a (x ∷ xs) zs → bar zs
prop3 b zs Ra = bar2 [] (prop1 zs)

higman : bar []
higman = bar2 [] (bar2 [] (bar1 (good0 (L0 ⊴-[]))))

data is-prefix {A : Set} (f : ℕ → A) : List A → Set where
  is-prefix-[] : is-prefix f []
  is-prefix-∷  : (xs : List A) →
        is-prefix f xs → is-prefix f (f (length xs) ∷ xs)

is-prefix-x : ∀ {A : Set} {f} {x : A} {xs} →
                is-prefix f (x ∷ xs) → x ≡ f (length xs)
is-prefix-x (is-prefix-∷ p q) = refl

is-prefix-p : ∀ {A : Set} {f} {x : A} {xs} →
                is-prefix f (x ∷ xs) → is-prefix f xs
is-prefix-p (is-prefix-∷ p q) = q


test-is-prefix : is-prefix suc (3 ∷ 2 ∷ 1 ∷ [])
test-is-prefix =
  is-prefix-∷ (suc (suc zero) ∷ suc zero ∷ [])
              (is-prefix-∷ (suc zero ∷ []) (is-prefix-∷ [] is-prefix-[]))

good-prefix-lemma :
  ∀ ws → (f : ℕ → Word) →
    bar ws →
    is-prefix f ws →
    Σ (List Word) (λ vs → is-prefix f vs × good vs)
good-prefix-lemma ws f (bar1 good-ws) p = ws , p , good-ws
good-prefix-lemma ws f (bar2 w bar-w∷ws) p = {!!}

good-prefix :
  ∀ (f : ℕ → Word) →
    ‌Σ (List Word) (λ vs → (is-prefix f vs × good vs))
good-prefix f = good-prefix-lemma [] f higman is-prefix-[]
