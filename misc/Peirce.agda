open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Nullary using (¬_)

module Peirce where

-- We show that Peirce's law is equivalent to the Law of
-- Excluded Middle (EM).

peirce : Set₁
peirce = ∀ (P Q : Set) →  ((P → Q) → P) → P

em : Set₁
em = ∀ (R : Set) → R ⊎ ¬ R

peirce→em : peirce → em
peirce→em h R =
  h (R ⊎ (R → ⊥)) ⊥
    (λ n-rnr → inj₂ (λ r → n-rnr (inj₁ r))) 

em→peirce : em → peirce
em→peirce e P Q h with e P
em→peirce e P Q h | inj₁  p = p
em→peirce e P Q h | inj₂ ¬p = h (λ p → ⊥-elim (¬p p))
