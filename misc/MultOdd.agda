module MultOdd where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Unit

open import Function
open import Function.Related as Related

open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality as P
  hiding (sym)

open import Algebra
  using (module CommutativeSemiring)

module *+ =
  CommutativeSemiring Data.Nat.Properties.commutativeSemiring

mutual

  data Even : ℕ → Set where
    even0 : Even zero
    even1 : {n : ℕ} → (prev-odd : Odd n) → Even (suc n)

  data Odd : ℕ → Set where
    odd1 : {n : ℕ} → (prev-even : Even n) → Odd (suc n)

-- even-2n

even-2n : ∀ n → Even (n + n)

even-2n zero = even0

even-2n (suc n) = helper (even-2n n)
  where
  open Related.EquationalReasoning
  helper =
    Even (n + n)
      ∼⟨ even1 ∘ odd1 ⟩
    Even (suc (suc (n + n)))
      ∼⟨ subst (Even ∘ suc) (*+.+-comm (suc n) n) ⟩
    Even (suc (n + suc n))
    ∎

-- even + even → even
-- even + odd  → odd
-- odd  + even → odd
-- odd  + odd  → even

even+even : ∀ {m n} → Even m → Even n → Even (m + n)
even+odd : ∀ {m n} → Even m → Odd n → Odd (m + n)
odd+even : ∀ {m n} → Odd m → Even n → Odd (m + n)
odd+odd : ∀ {m n} → Odd m → Odd n → Even (m + n)

even+even even0 hn = hn
even+even (even1 prev-odd) hn = even1 (odd+even prev-odd hn)

even+odd even0 hn = hn
even+odd (even1 prev-odd) hn = odd1 (odd+odd prev-odd hn) 

odd+even (odd1 prev-even) hn = odd1 (even+even prev-even hn)

odd+odd (odd1 prev-even) hn = even1 (even+odd prev-even hn)

-- odd  * odd → odd
-- even * odd → even

odd*odd : ∀ {m n} → Odd m → Odd n → Odd (m * n)
even*odd : ∀ {m n} → Even m → Odd n → Even (m * n)

odd*odd {n = n} (odd1 {m} prev-even) hn =
  odd+even hn (even*odd prev-even hn)

even*odd even0 hn = even0  
even*odd {n = n} (even1 {m} prev-odd) hn =
  odd+odd hn (odd*odd prev-odd hn)

-- multOdd

multOdd : {xs : List ℕ} → All Odd xs → Odd (foldr _*_ 1 xs)

multOdd [] =
  odd1 even0
multOdd (px ∷ pxs) =
  odd*odd px (multOdd pxs)

--
