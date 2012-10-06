open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Nat
open import Function using ( _∘_; flip )


open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming([_] to ≡[_])

open ≡-Reasoning

module Imp where

module AExpM where

data AExp : Set where
  aNum   : ℕ → AExp
  aPlus  : AExp → AExp → AExp
  aMinus : AExp → AExp → AExp
  aMult  : AExp → AExp → AExp

data BExp : Set where
  bTrue  : BExp
  bFalse : BExp
  bEq    : AExp → AExp → BExp
  bLe    : AExp → AExp → BExp
  bNot   : BExp → BExp
  bAnd   : BExp → BExp → BExp

aeval : AExp → ℕ
aeval (aNum n)       = n
aeval (aPlus a1 a2)  = aeval a1 + aeval a2
aeval (aMinus a1 a2) = aeval a1 ∸ aeval a2
aeval (aMult a1 a2)  = aeval a1 * aeval a2


test_aeval1 : aeval (aPlus (aNum 2) (aNum 2)) ≡ 4
test_aeval1 = refl

beval : BExp → Bool
beval bTrue        = true
beval bFalse       = false
beval (bEq a1 a2)  = ⌊ aeval a1 ≟ aeval a2 ⌋ 
beval (bLe a1 a2)  = ⌊ aeval a1 ≤? aeval a2 ⌋
beval (bNot b1)    = not (beval b1)
beval (bAnd b1 b2) = beval b1 ∧ beval b2

0+⟦_⟧ : AExp → AExp
0+⟦ aNum n ⟧ =
  aNum n
0+⟦ aPlus (aNum 0) e2 ⟧ =
  0+⟦ e2 ⟧
0+⟦ aPlus e1 e2 ⟧ =
  aPlus 0+⟦ e1 ⟧ 0+⟦ e2 ⟧
0+⟦ aMinus e1 e2 ⟧ =
  aMinus 0+⟦ e1 ⟧ 0+⟦ e2 ⟧
0+⟦ aMult e1 e2 ⟧ =
  aMult 0+⟦ e1 ⟧ 0+⟦ e2 ⟧


test_optimize_0plus :
  0+⟦ aPlus (aNum 2) (aPlus (aNum 0)
                            (aPlus (aNum 0) (aNum 1))) ⟧
  ≡ aPlus (aNum 2) (aNum 1)
test_optimize_0plus = refl

mutual
  0+⇊⟦_,_⟧_ : (e1 e2 : AExp) → (op : ℕ → ℕ → ℕ) →
    op (aeval 0+⟦ e1 ⟧) (aeval 0+⟦ e2 ⟧) ≡ op (aeval e1) (aeval e2)
  0+⇊⟦ e1 , e2 ⟧ op =
    begin
      op (aeval 0+⟦ e1 ⟧) (aeval 0+⟦ e2 ⟧)
        ≡⟨ cong (flip op (aeval 0+⟦ e2 ⟧)) 0+-sound⟦ e1 ⟧  ⟩
      op (aeval e1) (aeval 0+⟦ e2 ⟧)
        ≡⟨ cong (op (aeval e1)) 0+-sound⟦ e2 ⟧ ⟩
      op (aeval e1) (aeval e2)
    ∎

  0+-sound⟦_⟧ : (e : AExp) → aeval 0+⟦ e ⟧ ≡ aeval e
  0+-sound⟦ aNum n ⟧ = refl
  0+-sound⟦ aPlus (aNum zero) e2 ⟧ =
    0+-sound⟦ e2 ⟧
  0+-sound⟦ aPlus (aNum (suc n)) e2 ⟧ =
    cong (λ z → suc (n + z)) 0+-sound⟦ e2 ⟧
  0+-sound⟦ aPlus (aPlus e11 e12) e2 ⟧ =
    0+⇊⟦ aPlus e11 e12 , e2 ⟧ _+_
  0+-sound⟦ aPlus (aMinus e11 e12) e2 ⟧ =
    0+⇊⟦ aMinus e11 e12 , e2 ⟧ _+_
  0+-sound⟦ aPlus (aMult e11 e12) e2 ⟧ =
    0+⇊⟦ aMult e11 e12 , e2 ⟧ _+_
  0+-sound⟦ aMinus e1 e2 ⟧ =
    0+⇊⟦ e1 , e2 ⟧ _∸_
  0+-sound⟦ aMult e1 e2 ⟧ =
    0+⇊⟦ e1 , e2 ⟧ _*_

