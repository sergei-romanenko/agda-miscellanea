module GeneralRec where

  open import Data.Nat
  open import Data.Bool
  open import Data.List hiding (partition)
  open import Data.Product
  open import Data.Empty

  open import Data.Stream

  open import Relation.Nullary
  open import Relation.Unary hiding (Decidable)
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
    renaming ([_] to ≡[_])

  open import Function
  open import Induction
  open import Induction.WellFounded
  open import Coinduction

  open ≡-Reasoning

  partition : {A : Set} (xs : List A) → List A × List A
  partition [] = [] , []
  partition (x ∷ []) = [ x ] , []
  partition (x₁ ∷ x₂ ∷ xs) with partition xs
  partition (x₁ ∷ x₂ ∷ xs) | xs₁ , xs₂ =
    x₁ ∷ xs₁ , x₂ ∷ xs₂

  module MergeSort (A : Set) (le : A → A → Bool) where
  
    insert : (a : A) (xs : List A) → List A
    insert a [] = [ a ]
    insert a (x ∷ xs) with le a x
    ... | true = a ∷ xs
    ... | false = x ∷ insert a xs

    merge : (xs ys : List A) → List A
    merge [] ys = ys
    merge (x ∷ xs) ys = insert x (merge xs ys)

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

  <′-ℕ-wf : Well-founded _<′_
  <′-ℕ-wf x = acc (help x)
    where help : ∀ x y → y <′ x → Acc (_<′_) y
          help .(suc y) y ≤′-refl = <′-ℕ-wf y
          help .(suc x) y (≤′-step {x} m≤′n) = help x y m≤′n

  ≤-refl : ∀ {n} → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step z≤n = z≤n
  ≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

  ≤′-≤ : ∀ {m n} → m ≤′ n → m ≤ n
  ≤′-≤ ≤′-refl = ≤-refl
  ≤′-≤ (≤′-step m≤′n) = ≤-step (≤′-≤ m≤′n)

  module Lenth-wf {A : Set} = Inverse-image {_} {List A} {ℕ} {_<′_} length
    renaming(accessible to length-acc; well-founded to length-wf )

  ≤′-zero : ∀ {m} → 0 ≤′ m
  ≤′-zero {zero} = ≤′-refl
  ≤′-zero {suc n} = ≤′-step ≤′-zero

  ≤′-suc : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
  ≤′-suc ≤′-refl = ≤′-refl
  ≤′-suc (≤′-step m≤′n) = ≤′-step (≤′-suc m≤′n)

  ≤-≤′ : ∀ {m n} → m ≤ n → m ≤′ n
  ≤-≤′ z≤n = ≤′-zero
  ≤-≤′ (s≤s m≤n) = ≤′-suc (≤-≤′ m≤n)

  s≤′-elim : ∀ {m n} → suc m ≤′ n → m ≤′ n
  s≤′-elim ≤′-refl = ≤′-step ≤′-refl
  s≤′-elim (≤′-step m≤′n) = ≤′-step (s≤′-elim m≤′n)

  _≤′?_ : Decidable _≤′_
  m ≤′? n with m ≤? n
  ... | yes m≤n = yes (≤-≤′ m≤n)
  ... | no ¬m≤n = no  (λ m≤′n → ¬m≤n (≤′-≤ m≤′n))

  module Partition-lemma {A : Set} where
    _≼_ : List A → List A → Set
    xs ≼ ys = length xs ≤′ length ys
 
    partition-size : ∀ (zs : List A) l →
                     2 ≤′ length zs → length zs ≤′ l →
                     proj₁ (partition zs) ≼ zs × proj₂ (partition zs) ≼ zs
    partition-size [] l 2≤len len≤l = ≤′-refl , ≤′-refl
    partition-size (x ∷ []) l 2≤len len≤l = ≤′-refl , ≤′-step ≤′-refl
    partition-size (x ∷ y ∷ zs) l 2≤len len≤l with 2 ≤′? length zs
    partition-size (x ∷ y ∷ zs) l 2≤len len≤l | yes 2≤len'
      with partition-size zs l 2≤len' (s≤′-elim (s≤′-elim len≤l))
    partition-size (x ∷ y ∷ zs) l 2≤len len≤l | yes 2≤len' | s₁ , s₂ =
      ≤′-suc (≤′-step s₁) , ≤′-suc (≤′-step s₂)
    partition-size (x ∷ y ∷ []) l 2≤len len≤l | no ¬2≤len' =
      ≤′-step ≤′-refl , ≤′-step ≤′-refl
    partition-size (x ∷ y ∷ x' ∷ []) l 2≤len len≤l | no ¬2≤len' =
      2≤len , ≤′-step (≤′-step ≤′-refl)
    partition-size (x ∷ y ∷ x' ∷ y' ∷ zs) l 2≤len len≤l | no ¬2≤len' =
      ⊥-elim (¬2≤len' (≤′-suc (≤′-suc ≤′-zero)))
