open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Nat
open import Data.Product
open import Data.Empty

open import Function using ( _∘_; flip )

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming([_] to ≡[_])

open ≡-Reasoning

module Imp where

data ABo : Set where
  plus  : ABo
  minus : ABo
  mult  : ABo

_≟abo_ : (b1 : ABo) → (b2 : ABo) → Dec (b1 ≡ b2)
plus  ≟abo plus  = yes refl
plus  ≟abo minus = no (λ ())
plus  ≟abo mult  = no (λ ())
minus ≟abo plus  = no (λ ())
minus ≟abo minus = yes refl
minus ≟abo mult  = no (λ ())
mult  ≟abo plus  = no (λ ())
mult  ≟abo minus = no (λ ())
mult  ≟abo mult  = yes refl

data AExp : Set where
  aConst : ℕ → AExp
  aBinop : ABo → AExp → AExp → AExp

aConst-n : ∀ {n1 n2} → aConst n1 ≡ aConst n2 → n1 ≡ n2
aConst-n refl = refl

aBinop-b : ∀ {b e1 e2 b' e1' e2'} → aBinop b e1 e2 ≡ aBinop b' e1' e2' →
             b ≡ b'
aBinop-b refl = refl

aBinop-e1 : ∀ {b e1 e2 b' e1' e2'} → aBinop b e1 e2 ≡ aBinop b' e1' e2' →
               e1 ≡ e1'
aBinop-e1 refl = refl

aBinop-e2 : ∀ {b e1 e2 b' e1' e2'} → aBinop b e1 e2 ≡ aBinop b' e1' e2' →
               e2 ≡ e2'
aBinop-e2 refl = refl

_≟aexp_ : (e1 : AExp) → (e2 : AExp) → Dec (e1 ≡ e2)
aConst n ≟aexp aConst n' with n ≟ n'
aConst n ≟aexp aConst n' | yes n≡n' = yes (cong aConst n≡n')
aConst n ≟aexp aConst n' | no n≢n' = no (n≢n' ∘ aConst-n)
aConst _  ≟aexp aBinop _ _ _ = no (λ ())
aBinop _ _ _ ≟aexp aConst _ = no (λ ())
aBinop b e1 e2 ≟aexp aBinop b' e1' e2' with b ≟abo b'
aBinop .b' e1 e2 ≟aexp aBinop b' e1' e2' | yes refl with e1 ≟aexp e1'
aBinop .b' e1 e2 ≟aexp aBinop b' e1' e2' | yes refl | yes e1≡e1'
  with e2 ≟aexp e2'
aBinop .b' e1 e2 ≟aexp aBinop b' e1' e2' | yes refl | yes e1≡e1' | yes e2≡e2'
  = yes (begin
           aBinop b' e1 e2 ≡⟨ cong (aBinop b' e1) e2≡e2' ⟩
           aBinop b' e1 e2' ≡⟨ cong (λ z → aBinop b' z e2') e1≡e1' ⟩
           aBinop b' e1' e2'
        ∎)
aBinop .b' e1 e2 ≟aexp aBinop b' e1' e2' | yes refl | yes e1≡e1' | no e2≢e2' =
       no (e2≢e2' ∘ aBinop-e2)
aBinop .b' e1 e2 ≟aexp aBinop b' e1' e2' | yes refl | no e1≢e1' =
       no (e1≢e1' ∘ aBinop-e1)
aBinop b e1 e2 ≟aexp aBinop b' e1' e2' | no b≢b' =
       no (b≢b' ∘ aBinop-b)

⟦_⟧abo : ABo → ℕ → ℕ → ℕ
⟦ plus  ⟧abo = _+_
⟦ minus ⟧abo = _∸_
⟦ mult  ⟧abo = _*_

aeval : AExp → ℕ
aeval (aConst n)       = n
aeval (aBinop b a1 a2) = ⟦ b ⟧abo (aeval a1) (aeval a2)

test_aeval1 : aeval (aBinop plus (aConst 2) (aConst 2)) ≡ 4
test_aeval1 = refl

--------------------

×-dec : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P × Q)
×-dec (yes p) (yes q) = yes (p , q)
×-dec (no ¬p) _       = no (λ p×q → ¬p (proj₁ p×q))
×-dec _       (no ¬q) = no (λ p×q → ¬q (proj₂ p×q))

0+dec : (b : ABo) → (e : AExp) → Dec ((b ≡ plus) × (e ≡ aConst 0))
0+dec b e = ×-dec (b ≟abo plus) (e ≟aexp aConst 0)

0+⟦_⟧ : AExp → AExp
0+⟦ aConst n ⟧ = aConst n
0+⟦ aBinop b e1 e2 ⟧ with 0+dec b e1
... | yes _ = 0+⟦ e2 ⟧
... | no _ = aBinop b 0+⟦ e1 ⟧ 0+⟦ e2 ⟧

test_0+ :
  0+⟦ aBinop plus (aConst 2) (aBinop plus (aConst 0)
                             (aBinop plus (aConst 0) (aConst 1))) ⟧
  ≡ aBinop plus (aConst 2) (aConst 1)
test_0+ = refl

0+-sound⟦_⟧ : (e : AExp) → aeval 0+⟦ e ⟧ ≡ aeval e
0+-sound⟦ aConst n ⟧ = refl
0+-sound⟦ aBinop b e1 e2 ⟧ with 0+dec b e1
0+-sound⟦ aBinop b e1 e2 ⟧ | yes (b≡plus , e1≡0) =
  begin
    aeval 0+⟦ e2 ⟧
      ≡⟨ 0+-sound⟦ e2 ⟧ ⟩
     ⟦ plus ⟧abo (aeval (aConst 0)) (aeval e2)
      ≡⟨ cong (λ x → ⟦ x ⟧abo (aeval (aConst 0)) (aeval e2)) (sym b≡plus) ⟩
     ⟦ b ⟧abo (aeval (aConst 0)) (aeval e2)
      ≡⟨ cong (λ e → ⟦ b ⟧abo (aeval e) (aeval e2)) (sym e1≡0) ⟩
     ⟦ b ⟧abo (aeval e1) (aeval e2)
  ∎
0+-sound⟦ aBinop b e1 e2 ⟧ | no _ =
  begin
    ⟦ b ⟧abo (aeval 0+⟦ e1 ⟧) (aeval 0+⟦ e2 ⟧)
      ≡⟨ cong (λ e → ⟦ b ⟧abo e (aeval 0+⟦ e2 ⟧)) 0+-sound⟦ e1 ⟧ ⟩
    ⟦ b ⟧abo (aeval e1) (aeval 0+⟦ e2 ⟧)
      ≡⟨ cong (λ e → ⟦ b ⟧abo (aeval e1) e) 0+-sound⟦ e2 ⟧ ⟩
    ⟦ b ⟧abo (aeval e1) (aeval e2)
  ∎

--------------------

data _⇓_ : AExp → ℕ → Set where
  eConst : ∀ (n : ℕ) →
             (aConst n) ⇓ n
  eBinop : ∀ (b : ABo) → (e1 e2 : AExp) → (n1 n2 : ℕ) →
             (e1 ⇓ n1) → (e2 ⇓ n2) →
             (aBinop b e1 e2) ⇓ (⟦ b ⟧abo n1 n2)

aeval→aevalR : ∀ e n → aeval e ≡ n → (e ⇓ n)
aeval→aevalR (aConst n) .n refl = eConst n
aeval→aevalR (aBinop b e1 e2) ._ refl =
  eBinop b e1 e2 n1 n2 r1 r2
  where n1 = aeval e1
        n2 = aeval e2
        n  = ⟦ b ⟧abo n1 n2
        r1 = aeval→aevalR e1 n1 refl 
        r2 = aeval→aevalR e2 n2 refl

aevalR→aeval : ∀ e n → (e ⇓ n) → aeval e ≡ n
aevalR→aeval (aConst .n) n (eConst .n) = refl
aevalR→aeval (aBinop b e1 e2) ._ (eBinop .b .e1 .e2 n1 n2 r1 r2) =
  begin
    ⟦ b ⟧abo (aeval e1) (aeval e2)
      ≡⟨ cong (flip ⟦ b ⟧abo (aeval e2)) (aevalR→aeval e1 n1 r1) ⟩ 
    ⟦ b ⟧abo n1 (aeval e2)
      ≡⟨ cong (⟦ b ⟧abo n1) (aevalR→aeval e2 n2 r2) ⟩ 
    ⟦ b ⟧abo n1 n2
  ∎

aeval⟷aevalR : ( ∀ e n → aeval e ≡ n → (e ⇓ n) ) ×
                   ( ∀ e n → (e ⇓ n) → aeval e ≡ n ) 
aeval⟷aevalR = aeval→aevalR , aevalR→aeval

{-
data BBo : Set where
  eq :  BBo
  le :  BBo
  and : BBo

data BExp : Set where
  bConst : Bool → BExp
  bBinop : BBo → AExp → AExp → BExp
  bNot   : BExp → BExp
-}

{-
beval : BExp → Bool
beval (bConst v) = v
beval (bBinop b e1 e2) = {!!}
beval (bNot y) = {!!}

beval : BExp → Bool
beval bTrue        = true
beval bFalse       = false
beval (bEq a1 a2)  = ⌊ aeval a1 ≟ aeval a2 ⌋ 
beval (bLe a1 a2)  = ⌊ aeval a1 ≤? aeval a2 ⌋
beval (bNot b1)    = not (beval b1)
beval (bAnd b1 b2) = beval b1 ∧ beval b2
-}
