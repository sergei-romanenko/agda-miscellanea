module Inspect where

open import Relation.Binary.PropositionalEquality renaming ([_] to [_]ⁱ)
open import Data.Bool
open import Data.List hiding (filter)
open import Data.List.All using ( All; []; _∷_ )
open import Data.Unit

import Level

open ≡-Reasoning
open import Function

-- Filter

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter _ [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

filter-map : ∀ {a b} {A : Set a} {B : Set b}
             (f : A → B) (p : B → Bool) (xs : List A) →
             filter p (map f xs) ≡ map f (filter (p ∘ f) xs)
filter-map f p [] = refl
filter-map f p (x ∷ xs) with p (f x)
... | true = cong (_∷_ (f x)) (filter-map f p xs)
... | false = filter-map f p xs

filter-filter : ∀ {a} {A : Set a}
                (p : A → Bool) (xs : List A) →
                filter p (filter p xs) ≡ filter p xs
filter-filter p [] = refl
filter-filter p (x ∷ xs) with p x | inspect p x
... | true  | [ px≡true  ]ⁱ rewrite px≡true =
  cong (_∷_ x) (filter-filter p xs)
... | false | [ px≡false ]ⁱ =
  filter-filter p xs

sat : {A : Set} → (A → Bool) → A → Set
sat p x = T(p x)

-- Find

data Find {A : Set} (p : A → Bool) : List A → Set where
  found  : (xs : List A) (x : A) → sat p x → (ys : List A) →
               Find p (xs ++ x ∷ ys)
  ¬found : ∀ {xs} → All (sat (not ∘ p)) xs → Find p xs

find : {A : Set} (p : A → Bool) (xs : List A) → Find p xs
find p [] = ¬found []
find p (x ∷ xs) with p x | inspect p x
find p (x ∷ xs) | true | [ px≡true ]ⁱ =
  found [] x (subst T (sym px≡true) tt)  xs
find p (x ∷ xs) | false | [ px≡false ]ⁱ with find p xs
find p (x' ∷ .(xs ++ x ∷ ys)) | false | [ px≡false ]ⁱ | found xs x y ys =
  found (x' ∷ xs) x y ys
find p (x ∷ xs) | false | [ px≡false ]ⁱ | ¬found npxs =
  ¬found (subst (T ∘ not) (sym px≡false) tt ∷ npxs)
