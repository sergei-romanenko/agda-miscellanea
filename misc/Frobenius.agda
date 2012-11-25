module Frobenius where

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Function

open import Relation.Nullary

infix 1 _↔_

_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
_↔_ P Q = (P → Q) × (Q → P)

em : Set₁
em = ∀ (R : Set) → R ⊎ ¬ R

frobenius⇒ : ∀ {A : Set} {P : A → Set} {Q : Set} →
  Σ A (λ x → Q × P x) → Q × Σ A (λ x → P x)
frobenius⇒ (x , (q , px)) = q , (x , px)

frobenius⇐ : ∀ {A : Set} {P : A → Set} {Q : Set} →
  Q × Σ A (λ x → P x) → Σ A (λ x → Q × P x)
frobenius⇐ (q , (x , px)) = x , (q , px)

frobenius : ∀ {A : Set} {P : A → Set} {Q : Set} →
  (∃ λ x → Q × P x) ↔ Q × (∃ λ x → P x)
frobenius = frobenius⇒ , frobenius⇐

frobenius-dual⇒ : Set₁
frobenius-dual⇒ = ∀ {A : Set} {P : A → Set} {Q : Set} →
                   (∀ x → Q ⊎ P x) → Q ⊎ (∀ x → P x)

frobenius-dual⇐ : Set₁
frobenius-dual⇐ = ∀ {A : Set} {P : A → Set} {Q : Set} →
                   Q ⊎ (∀ x → P x) → (∀ x → Q ⊎ P x)

frobenius-dual : Set₁
frobenius-dual = frobenius-dual⇒ × frobenius-dual⇐

em→frobenius-dual⇒ : em → frobenius-dual⇒
em→frobenius-dual⇒ em {Q = Q} h =
  [ (λ q → inj₁ q) ,
    (λ ¬q → inj₂ (λ x → [ (λ q → ⊥-elim (¬q q)) , id ]′ (h x))) ]′
  (em Q)

em→frobenius-dual⇐ : em → frobenius-dual⇐
em→frobenius-dual⇐ em =
  [ (λ q a → inj₁ q) , (λ p a → inj₂ (p a)) ]′

em→frobenius-dual : em → ∀ {A : Set} {P : A → Set} {Q : Set} →
                              (∀ x → Q ⊎ P x) ↔ Q ⊎ (∀ x → P x)
em→frobenius-dual em = em→frobenius-dual⇒ em , em→frobenius-dual⇐ em

frobenius-dual→em : frobenius-dual → em
frobenius-dual→em (f⇒ , f⇐) R = f⇒ (λ r → f⇐ (inj₁ r) (r ∶ R) ∶ R ⊎ ⊥)
