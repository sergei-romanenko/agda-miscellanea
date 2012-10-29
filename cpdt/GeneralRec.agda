module GeneralRec where

  open import Data.Nat
  open import Data.Bool
  open import Data.List hiding (partition)
  open import Data.Product
  open import Data.Empty

  open import Data.Stream

  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary

  open import Function
  open import Induction
  open import Induction.WellFounded
  open import Coinduction

  module MergeSort (A : Set) (le : A → A → Bool) where
  
    insert : (a : A) (xs : List A) → List A
    insert a [] = [ a ]
    insert a (x ∷ xs) with le a x
    ... | true = a ∷ xs
    ... | false = x ∷ insert a xs

    merge : (xs ys : List A) → List A
    merge [] ys = ys
    merge (x ∷ xs) ys = insert x (merge xs ys)

    partition : (xs : List A) → List A × List A
    partition [] = [] , []
    partition (x ∷ []) = [ x ] , []
    partition (x₁ ∷ x₂ ∷ xs) with partition xs
    partition (x₁ ∷ x₂ ∷ xs) | xs₁ , xs₂ =
      x₁ ∷ xs₁ , x₂ ∷ xs₂

  module MergeSort₁ (A : Set) (le : A → A → Bool) where
    open module ms = MergeSort A le

    mergeSort : (xs : List A) → List A
    mergeSort xs with (length xs) ≤? 2
    mergeSort xs | yes _ = xs
    mergeSort xs | no  _ with partition xs
    ... | xs₁ , xs₂ = merge (mergeSort xs₁) (mergeSort xs₂)

-- When using well-founded recursion you can recurse arbitrarily, as
-- long as the arguments become smaller, and "smaller" is
-- well-founded.
{-
WfRec : ∀ {a} {A : Set a} → Rel A a → RecStruct A
WfRec _<_ P x = ∀ y → y < x → P y
-}
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
{-
data Acc {a} {A : Set a} (_<_ : Rel A a) (x : A) : Set a where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x
-}
-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
{-
Well-founded : ∀ {a} {A : Set a} → Rel A a → Set a
Well-founded _<_ = ∀ x → Acc _<_ x
-}

{-
  data IsChain {A} (R : A → A → Set) : Stream A → Set where
    chainCons : ∀ (x y : A) {s : Stream A} → R y x →
      IsChain R (y ∷ ♯ s ) →
      IsChain R (x ∷ ♯ (y ∷ ♯ s))

  noChains' : ∀ {A} (R : A → A → Set) {x} → Acc R x → ∀ {s} →
                ¬ IsChain R (x ∷ s)
  noChains' R {x} (acc rs) (chainCons .x y Ryx ch-y) = {!!}
-}

  <′-ℕ-wf : Well-founded _<′_
  <′-ℕ-wf x = acc (help x)
    where help : ∀ x y → y <′ x → Acc (_<′_) y
          help .(suc y) y ≤′-refl = <′-ℕ-wf y
          help .(suc n) y (≤′-step {n} m≤′n) = help n y m≤′n

  module Inverse-image-Well-founded
         {ℓ} {A B : Set ℓ} (_<_ : Rel B ℓ) (f : A → B)
    where

    _≺_ : Rel A ℓ
    x ≺ y = f x < f y

    ii-acc : ∀ {x} → Acc _<_ (f x) → Acc _≺_ x
    ii-acc (acc g) = acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

    ii-wf : Well-founded _<_ →  Well-founded _≺_
    ii-wf wf x = ii-acc (wf (f x))

  module length-wf {A} where
    open Inverse-image-Well-founded {_}{List A} _<′_ length public

    wf : Well-founded _≺_
    wf = ii-wf <′-ℕ-wf

