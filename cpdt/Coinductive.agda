open import Data.Bool
open import Data.Nat
open import Data.List

open import Relation.Binary.PropositionalEquality

open import Coinduction

module Coinductive where

data Stream (A : Set) : Set where
  _∷_ : A -> ∞ (Stream A) -> Stream A

zeroes : Stream ℕ
zeroes =  0 ∷ ♯ zeroes

mutual

  trues-falses : Stream Bool
  trues-falses = true ∷ ♯ falses-trues

  falses-trues : Stream Bool
  falses-trues = false ∷ ♯ trues-falses

approx : {A : Set} → (s : Stream A) → (n : ℕ) → List A
approx s zero = []
approx (x ∷ xs) (suc n) = x ∷ approx (♭ xs) n

test-approx₁ :
  approx zeroes 10 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
test-approx₁ = refl

test-approx₂ :
  approx trues-falses 5 ≡ true ∷ false ∷ true ∷ false ∷ true ∷ []
test-approx₂ = refl

-- looper : Stream ℕ
-- looper = looper

map-stream : {A B : Set} → (f : A -> B) → Stream A → Stream B
map-stream f (x ∷ xs) = f x ∷ ♯(map-stream f (♭ xs))

interleave : {A : Set} → Stream A → Stream A → Stream A
interleave (x ∷ xs) (y ∷ ys) = x ∷ ♯(y ∷ ♯ interleave (♭ xs) (♭ ys))

ones : Stream ℕ
ones = 1 ∷ ♯ ones

ones' : Stream ℕ
ones' = map-stream suc zeroes

-- Bisimilarity

infix 4 _≈_

data _≈_ {A : Set} : Stream A → Stream A → Set where
  _∷_ : ∀ x {xs ys} → ∞ (♭ xs ≈ ♭ ys) → x ∷ xs ≈ x ∷ ys

ones-eq : ones ≈ ones'
ones-eq = suc zero ∷ ♯ ones-eq

refl≈ : ∀ {A} → (as : Stream A) → as ≈ as
refl≈ (a ∷ as) = a ∷ ♯ refl≈ (♭ as)

--sym≈ : ∀ {A} → (as bs : Stream A) → as ≈ bs → bs ≈ as
--sym≈ (.b ∷ as) (b ∷ bs) (.b ∷ as≈bs) = b ∷ ♯ sym≈ (♭ as) (♭ bs) (♭ as≈bs)

sym≈ : ∀ {A} → {as bs : Stream A} → as ≈ bs → bs ≈ as
sym≈ (a ∷ as≈bs) = a ∷ ♯ sym≈ (♭ as≈bs)

trans≈ : ∀ {A} → {as bs cs : Stream A} → as ≈ bs → bs ≈ cs → as ≈ cs
trans≈ (a ∷ as≈bs) (.a ∷ bs≈cs) = a ∷ ♯ trans≈ (♭ as≈bs) (♭ bs≈cs)


fact : ℕ → ℕ
fact zero = 1
fact (suc n) = suc n * fact n

fact-slow' : ℕ → Stream ℕ
fact-slow' n = fact n ∷ ♯ fact-slow' (suc n)

fact-slow = fact-slow' 1

fact-iter' : ℕ → ℕ → Stream ℕ
fact-iter' cur acc = acc ∷ ♯(fact-iter' (suc cur) (cur * acc))

fact-iter = fact-iter' 2 1

test-fact-slow : approx fact-iter 5 ≡ 1 ∷ 2 ∷ 6 ∷ 24 ∷ 120 ∷ []
test-fact-slow = refl

test-fact-iter : approx fact-iter 5 ≡ 1 ∷ 2 ∷ 6 ∷ 24 ∷ 120 ∷ []
test-fact-iter = refl

fact-eq' : ∀ n → fact-iter' (suc n) (fact n) ≈ fact-slow' n
fact-eq' n = fact n ∷ ♯ fact-eq' (suc n)

fact-eq : fact-iter ≈ fact-slow
fact-eq =  1 ∷ (♯ fact-eq' 2)
