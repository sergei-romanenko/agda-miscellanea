open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Nullary using (¬_)

module Peirce where

-- We show that Peirce's law is equivalent to the Law of
-- Excluded Middle (EM).

peirce : Set₁
peirce = ∀ (P Q : Set) → ((P → Q) → P) → P

em : Set₁
em = ∀ (R : Set) → R ⊎ ¬ R

peirce→em : peirce → em
peirce→em h R =
  h (R ⊎ (R → ⊥)) ⊥
    (λ n-rnr → inj₂ (λ r → n-rnr (inj₁ r))) 

em→peirce : em → peirce
em→peirce e P Q h with e P
... | inj₁  p = p
... | inj₂ ¬p = h (λ p → ⊥-elim (¬p p))

classic : Set₁
classic = ∀ (P : Set) → ¬ ¬ P → P

classic→em : classic → em
classic→em c R =
  c (R ⊎ (R → ⊥))
    (λ z → z (inj₂ (λ r → z (inj₁ r))))

em→classic : em → classic
em→classic e P with e P
em→classic e P | inj₁  p = λ ¬¬p → p
em→classic e P | inj₂ ¬p = λ ¬¬p → ⊥-elim (¬¬p ¬p)

de-Morgan-¬×¬ = ∀ (P Q : Set) → ¬(¬ P × ¬ Q) → P ⊎ Q

classic→de-Morgan-¬×¬ : classic → de-Morgan-¬×¬
classic→de-Morgan-¬×¬ c P Q r =
  c (P ⊎ Q) (λ ¬-p⊎q → r ((λ p → ¬-p⊎q (inj₁ p)) , (λ q → ¬-p⊎q (inj₂ q))))

de-Morgan-¬×¬→em : de-Morgan-¬×¬ → em
de-Morgan-¬×¬→em m R =
  m R (R → ⊥) (λ x → proj₂ x (proj₁ x))

de-Morgan-¬×¬→classic : de-Morgan-¬×¬ → classic
de-Morgan-¬×¬→classic m P ¬¬p =
  em→classic (de-Morgan-¬×¬→em m) P ¬¬p
