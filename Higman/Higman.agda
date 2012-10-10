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

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding([_])

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
  emb0 : ∀ (ys : Word) → [] ⊴ ys
  emb1 : ∀ (xs ys : List Letter) (y : Letter) →
           xs ⊴ ys → xs ⊴ y ∷ ys
  emb2 : ∀ (xs ys : List Letter) (x : Letter) →
         xs ⊴ ys → x ∷ xs ⊴ x ∷ ys

data L (v : Word) : List Word → Set where
  L0 : ∀ (w : Word) (ws : List Word) → w ⊴ v → L v (w ∷ ws)
  L1 : ∀ (w : Word) (ws : List Word) → L v ws → L v (w ∷ ws)

data good : List Word → Set where
  good0 : ∀ (ws : List Word) (w : Word) → L w ws → good (w ∷ ws)
  good1 : ∀ (ws : List Word) (w : Word) → good ws → good (w ∷ ws)

data R (a : Letter) : List Word → List Word → Set where
  R0 : R a [] []
  R1 : ∀ (vs ws : List Word) (w : Word) →
         R a vs ws → R a (w ∷ vs) ((a ∷ w) ∷ ws)

data T (a : Letter) : List Word → List Word → Set where
  T0 : ∀ (b : Letter) (w : Word) (ws zs : List Word) →
       a ≢L b → R b ws zs → T a (w ∷ zs) ((a ∷ w) ∷ zs)
  T1 : ∀ (w : Word) (ws zs : List Word) →
        T a ws zs → T a (w ∷ ws) ((a ∷ w) ∷ zs)
  T2 : ∀ (b : Letter) (w : Word) (ws zs : List Word) →
       a ≢L b → T a ws zs → T a ws ((b ∷ w) ∷ zs)

data bar : List Word → Set where
  bar1 : ∀ (ws : List Word) → good ws → bar ws
  bar2 : ∀ (ws : List Word) (w : Word) → bar (w ∷ ws) → bar ws

prop1 : ∀ (ws : List Word) → bar ([] ∷ ws)

prop1 ws =
  bar2 ([] ∷ ws) []
       (bar1 ([] ∷ [] ∷ ws) (good0 ([] ∷ ws) [] (L0 [] ws (emb0 []))))

lemma1 : ∀ (ws : List Word) (xs : Word) (x : Letter) →
         L xs ws → L (x ∷ xs) ws
lemma1 .(w ∷ ws) xs x (L0 w ws y) = L0 w ws (emb1 w xs x y)
lemma1 .(w ∷ ws) xs x (L1 w ws y) = L1 w ws (lemma1 ws xs x y)

lemma2' : ∀ (vs ws : List Word) (x : Letter) (xs : Word) →
          R x vs ws → L xs vs → L (x ∷ xs) ws
lemma2' .[] .[] x xs R0 ()
lemma2' .(w ∷ vs) .((x ∷ w) ∷ ws) x xs (R1 vs ws w y) (L0 .w .vs y') =
  L0 (x ∷ w) ws (emb2 w xs x y')
lemma2' .(w ∷ vs) .((x ∷ w) ∷ ws) x xs (R1 vs ws w y) (L1 .w .vs y') =
  L1 (x ∷ w) ws (lemma2' vs ws x xs y y')

lemma2 : ∀ (vs ws : List Word) (a : Letter) →
         R a vs ws → good vs → good ws
lemma2 .[] .[] a R0 Gvs = Gvs
lemma2 .(w ∷ vs) .((a ∷ w) ∷ ws) a (R1 vs ws w y) (good0 .vs .w y') =
  good0 ws (a ∷ w) (lemma2' vs ws a w y y')
lemma2 .(w ∷ vs) .((a ∷ w) ∷ ws) a (R1 vs ws w y) (good1 .vs .w y') =
  good1 ws (a ∷ w) (lemma2 vs ws a y y')

lemma3' : ∀ (vs ws : List Word) (x : Letter) (xs : Word) →
          T x vs ws → L xs vs → L (x ∷ xs) ws
lemma3' .(w ∷ zs) .((x ∷ w) ∷ zs) x xs (T0 b w ws zs y y') (L0 .w .zs y0) =
  L0 (x ∷ w) zs (emb2 w xs x y0)
lemma3' .(w ∷ zs) .((x ∷ w) ∷ zs) x xs (T0 b w ws zs y y') (L1 .w .zs y0) =
  L1 (x ∷ w) zs (lemma1 zs xs x y0)
lemma3' .(w ∷ ws) .((x ∷ w) ∷ zs) x xs (T1 w ws zs y) (L0 .w .ws y') =
  L0 (x ∷ w) zs (emb2 w xs x y')
lemma3' .(w ∷ ws) .((x ∷ w) ∷ zs) x xs (T1 w ws zs y) (L1 .w .ws y') =
  L1 (x ∷ w) zs (lemma3' ws zs x xs y y')
lemma3' vs .((b ∷ w) ∷ zs) x xs (T2 b w .vs zs y y') Lxsvs =
  L1 (b ∷ w) zs (lemma3' vs zs x xs y' Lxsvs)

lemma3 : ∀ (ws zs : List Word) (a : Letter) →
         T a ws zs → good ws → good zs
lemma3 .(w ∷ zs) .((a ∷ w) ∷ zs) a (T0 b w ws zs y y') (good0 .zs .w y0) =
  good0 zs (a ∷ w) (lemma1 zs w a y0)
lemma3 .(w ∷ zs) .((a ∷ w) ∷ zs) a (T0 b w ws zs y y') (good1 .zs .w y0) =
  good1 zs (a ∷ w) y0
lemma3 .(w ∷ ws) .((a ∷ w) ∷ zs) a (T1 w ws zs y) (good0 .ws .w y') =
  good0 zs (a ∷ w) (lemma3' ws zs a w y y')
lemma3 .(w ∷ ws) .((a ∷ w) ∷ zs) a (T1 w ws zs y) (good1 .ws .w y') =
  good1 zs (a ∷ w) (lemma3 ws zs a y y')
lemma3 ws .((b ∷ w) ∷ zs) a (T2 b w .ws zs y y') Gws =
  good1 zs (b ∷ w) (lemma3 ws zs a y' Gws)

lemma4 : ∀ (ws zs : List Word) (w : Word) (a : Letter) →
          R a (w ∷ ws) zs → T a (w ∷ ws) zs
lemma4 .[] .((lA ∷ w) ∷ []) w lA (R1 .[] .[] .w R0) =
  T0 lB w [] [] lA≢lB R0
lemma4 .(w' ∷ vs) .((lA ∷ w) ∷ (lA ∷ w') ∷ ws) w lA
       (R1 .(w' ∷ vs) .((lA ∷ w') ∷ ws) .w (R1 vs ws w' y)) =
  T1 w (w' ∷ vs) ((lA ∷ w') ∷ ws)
  (lemma4 vs ((lA ∷ w') ∷ ws) w' lA (R1 vs ws w' y))
lemma4 .[] .((lB ∷ w) ∷ []) w lB (R1 .[] .[] .w R0) =
  T0 lA w [] [] lB≢lA R0
lemma4 .(w' ∷ vs) .((lB ∷ w) ∷ (lB ∷ w') ∷ ws) w lB
       (R1 .(w' ∷ vs) .((lB ∷ w') ∷ ws) .w (R1 vs ws w' y)) =
  T1 w (w' ∷ vs) ((lB ∷ w') ∷ ws)
  (lemma4 vs ((lB ∷ w') ∷ ws) w' lB (R1 vs ws w' y))

letter≢ : ∀ (a b c : Letter) →
             a ≢L b → c ≢L a → c ≡ b
--letter≢ a b c a≢b c≢a = {!-c!}
letter≢ .lB lA .lA a≢b lA≢lB = refl
letter≢ .lA lA .lB () lB≢lA
letter≢ .lB lB .lA () lA≢lB
letter≢ .lA lB .lB a≢b lB≢lA = refl

_≟L_ : ∀ (a b : Letter) → Dec (a ≡ b)
--a ≟L b = {!!}
lA ≟L lA = yes refl
lA ≟L lB = no (λ ())
lB ≟L lA = no (λ ())
lB ≟L lB = yes refl

prop2 : ∀ (a b : Letter) (xs : List Word) →
        a ≢L b →
        bar xs →
        (ys : List Word) →
        bar ys →
        (zs : List Word) →
        T a xs zs → T b ys zs → bar zs
prop2 a b xs a≢b barxs ys barys zs Ta Tb =
  bar2 zs [] (prop1 zs)

prop3 : ∀ (a : Letter) (xs : List Word) (x : Word) →
        bar (x ∷ xs) →
        (zs : List Word) →
        R a (x ∷ xs) zs → bar zs
prop3 a xs x barxxs zs Ra = bar2 zs [] (prop1 zs)

higman : bar []
higman =
  bar2 [] []
    (bar2 ([] ∷ []) []
      (bar1 ([] ∷ [] ∷ []) (good0 ([] ∷ []) [] (L0 [] [] (emb0 [])))))

data is-prefix {A : Set} : List A → (ℕ → A) → Set where
  is-prefix-[] : ∀ (f : ℕ → A) → is-prefix [] f
  is-prefix-∷  : ∀ (f : ℕ → A) (x : A) (xs : List A) →
        x ≡ f (length xs) → is-prefix xs f → is-prefix (x ∷ xs) f

good-prefix-lemma :
  ∀ (ws : List Word) (f : ℕ → Word) →
    bar ws →
    is-prefix ws f →
    Σ (List Word) (λ vs → is-prefix vs f × good vs)
good-prefix-lemma ws f barws prewsf = {!!}

good-prefix :
  ∀ (f : ℕ → Word) →
    ‌Σ (List Word) (λ vs → (is-prefix vs f × good vs))
good-prefix f = {!!}