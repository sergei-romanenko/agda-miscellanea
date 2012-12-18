{-
    Title:      AFConstructions.Agda
    Author:     Sergei Romanenko, KIAM Moscow

    This Agda version is based on

    Dimitrios Vytiniotis, Thierry Coquand, and David Wahlstedt.   
    Stop when you are almost-full.  
    Adventures in constructive termination.  
    In Interactive Theorem Proving, ITP 2012. to appear.

    http://research.microsoft.com/en-us/people/dimitris/af-itp.pdf
    http://research.microsoft.com/en-us/people/dimitris/af-itp2012.tgz
    http://research.microsoft.com/en-us/people/dimitris/afchalmers.pptx
-}


module AFConstructions where

open import Data.Bool
open import Data.Sum
  renaming (map to map⊎)
open import Data.Product
  renaming (map to map×)
open import Data.Empty
open import Data.Unit
  using (⊤; tt)

open import Data.Nat
import Induction.Nat
open import Data.Nat.Properties
--open import Data.Fin

open import Relation.Nullary
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality

open import Function
open import Induction.WellFounded

import Level

open ≡-Reasoning

open import AlmostFull

--
-- Unions
--

af-union : ∀ {ℓ} {X : Set ℓ} (A B : Rel X ℓ) →
  Almost-full A → Almost-full (λ x y → A x y ⊎ B x y)
af-union A B afA = af-⇒ afA (λ x y → inj₁)

--
-- Intersections
-- (the intuitionistic version of Ramsey's theorem)
--

-- oplus-nullary

private

  cacb⇒cab : ∀ {ℓ} {X : Set ℓ} (C : Rel X ℓ) {A B : Set ℓ} {x y} →
                  C x y ⊎ A → C x y ⊎ B → C x y ⊎ A × B
  cacb⇒cab C (inj₁ c) _        = inj₁ c
  cacb⇒cab C _        (inj₁ c) = inj₁ c
  cacb⇒cab C (inj₂ a) (inj₂ b) = inj₂ (a , b)

oplus-nullary : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : Set ℓ} {CA : Rel X ℓ} →
  Almost-full CA → (∀ x y → CA x y → C x y ⊎ A) →
  Almost-full (λ x y → C x y ⊎ B) →
  Almost-full (λ x y → C x y ⊎ A × B)

oplus-nullary {C = C} (af-zt ra) ca⇒⊎ afB =
  af-⇒ afB (λ x y r → cacb⇒cab C (ca⇒⊎ x y (ra x y)) r)

oplus-nullary {C = C} afR ca⇒⊎ (af-zt rb) =
  af-⇒ afR (λ x y r → cacb⇒cab C (ca⇒⊎ x y r) (rb x y))

oplus-nullary {_} {X} {C} {A} {B} {CA} (af-sup sa) ca⇒⊎ (af-sup sb) =
  af-sup (λ u →
    af-⇒
      (oplus-nullary
        (sa u)
        (λ x y → [ (map⊎ inj₁ id) ∘ (ca⇒⊎ x y) ,
                    (map⊎ inj₂ id) ∘ (ca⇒⊎ u x) ]′
         ∶ (CA x y ⊎ CA u x → (C x y ⊎ C u x) ⊎ A))
        (af-⇒ (sb u) (λ x y → [ [ inj₁ ∘ inj₁ , inj₂ ]′ ,
                                  [ inj₁ ∘ inj₂ , inj₂ ]′ ]′
                       ∶ ((C x y ⊎ B) ⊎ C u x ⊎ B → (C x y ⊎ C u x) ⊎ B)))
        ∶ Almost-full (λ x y → (C x y ⊎ C u x) ⊎ A × B))
      (λ x y → [ [ inj₁ ∘ inj₁ , inj₂ ∘ inj₁ ]′ , inj₁ ∘ inj₂ ]′
         ∶ (((C x y ⊎ C u x) ⊎ A × B) → (C x y ⊎ A × B) ⊎ C u x ⊎ A × B))
 ∶ Almost-full (λ x y → (C x y ⊎ A × B) ⊎ C u x ⊎ A × B))

-- oplus-nullary-cor

oplus-nullary-cor : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : Set ℓ} → 
  Almost-full (λ x y → C x y ⊎ A) →
  Almost-full (λ x y → C x y ⊎ B) →
  Almost-full (λ x y → C x y ⊎ A × B)
oplus-nullary-cor afA afB =
  oplus-nullary afA (λ _ _ ca → ca) afB

-- oplus-unary

oplus-unary : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : X → Set ℓ} →
  {CA : Rel X ℓ} → Almost-full CA →
  (∀ x y → CA x y → C x y ⊎ A x) →
  {CB : Rel X ℓ} → (t : WFT X) → Almost-full# CB t →
  (∀ x y → CB x y → C x y ⊎ B x) →
  Almost-full (λ x y → C x y ⊎ (A x × B x))

oplus-unary-zt : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : X → Set ℓ} →
  {CA : Rel X ℓ} → (∀ x y → CA x y) →
  (∀ x y → CA x y → C x y ⊎ A x) →
  {CB : Rel X ℓ} → (t : WFT X) → Almost-full# CB t →
  (∀ x y → CB x y → C x y ⊎ B x) →
  Almost-full (λ x y → C x y ⊎ (A x × B x))

oplus-unary-?-sup : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : X → Set ℓ} →
  {CA : Rel X ℓ} → Almost-full CA →
  (∀ x y → CA x y → C x y ⊎ A x) →
  {CB : Rel X ℓ} → (g : ∀ x → WFT X) →
  Almost-full# CB (sup g) →
  (∀ x y → CB x y → C x y ⊎ B x) →
  Almost-full (λ x y → C x y ⊎ (A x × B x))

oplus-unary-sup-sup : ∀ {ℓ} {X : Set ℓ} {C : Rel X ℓ} {A B : X → Set ℓ} →
  {CA : Rel X ℓ} → (∀ u → Almost-full (λ x y → CA x y ⊎ CA u x)) →
  (∀ x y → CA x y → C x y ⊎ A x) →
  {CB : Rel X ℓ} → (g : ∀ x → WFT X) →
  Almost-full# CB (sup g) →
  (∀ x y → CB x y → C x y ⊎ B x) →
  Almost-full (λ x y → C x y ⊎ (A x × B x))

oplus-unary {C = C} (af-zt ra) ca⇒⊎ t afB cb⇒⊎ =
  oplus-unary-zt ra ca⇒⊎ t afB cb⇒⊎

oplus-unary {C = C} (af-sup sa) ca⇒⊎ zt (af-zt# rb) cb⇒⊎ =
  af-sup (λ u → af-⇒ (sa u) (λ x y →
    [ (λ caxy → inj₁ (cacb⇒cab C (ca⇒⊎ x y caxy) (cb⇒⊎ x y (rb x y)))) ,
      (λ caux → inj₂ (cacb⇒cab C (ca⇒⊎ u x caux) (cb⇒⊎ u x (rb u x)))) ]′))

oplus-unary (af-sup sa) ca⇒⊎ (sup g) (af-sup# .g sb) cb⇒⊎ =
  oplus-unary-sup-sup sa ca⇒⊎ g (af-sup# g sb) cb⇒⊎

oplus-unary-zt {C = C} ra ca⇒⊎ t afB cb⇒⊎ =
  af#⇒af
    (af#-⇒ t afB
      (λ x y cb → cacb⇒cab C (ca⇒⊎ x y (ra x y)) (cb⇒⊎ x y cb)))

oplus-unary-?-sup (af-zt r) ca⇒⊎ g (af-sup# .g sb) cb⇒⊎ =
 oplus-unary-zt (λ x y → ca⇒⊎ x y (r x y)) (λ x y z → z)
                (sup g) (af-sup# g sb) cb⇒⊎
oplus-unary-?-sup (af-sup sa) ca⇒⊎ g (af-sup# .g sb) cb⇒⊎ =
  oplus-unary-sup-sup sa ca⇒⊎ g (af-sup# g sb) cb⇒⊎

oplus-unary-sup-sup {_} {X} {C} {A} {B} {CA} sa ca⇒⊎ {CB}
                                         g (af-sup# .g sb) cb⇒⊎ =
  af-sup (λ u →
    af-⇒
      (oplus-nullary-cor (helper-a u) (helper-b u))
      (λ x y →
        [ [ [ inj₁ ∘ inj₁ , inj₁ ∘ inj₂ ]′ , inj₂ ∘ inj₁ ]′ , inj₂ ∘ inj₂ ]′)
        ∶ Almost-full (λ x y → (C x y ⊎ A x × B x) ⊎ C u x ⊎ A u × B u))
  where

    pqarbr : ∀ {ℓ} {P Q R A B : Set ℓ} →
               (P ⊎ Q) ⊎ (A ⊎ R) × (B ⊎ R) → ((P ⊎ A × B) ⊎ Q) ⊎ R
    pqarbr (inj₁ (inj₁ p)) = inj₁ (inj₁ (inj₁ p))
    pqarbr (inj₁ (inj₂ q)) = inj₁ (inj₂ q)
    pqarbr (inj₂ (inj₁ a , inj₁ b)) = inj₁ (inj₁ (inj₂ (a , b)))
    pqarbr (inj₂ (inj₁ _ , inj₂ r)) = inj₂ r
    pqarbr (inj₂ (inj₂ r , _)) = inj₂ r

    helper-a : ∀ u → 
      Almost-full (λ x y → ((C x y ⊎ A x × B x) ⊎ C u x) ⊎ A u)
    helper-a u =
      af-⇒
        (oplus-unary-?-sup
          (sa u)
          ((λ x y → [ [ inj₁ ∘ inj₁ , inj₂ ∘ inj₁ ]′ ∘ ca⇒⊎ x y ,
                       map⊎ inj₂ inj₂ ∘ ca⇒⊎ u x ]′)
          ∶ (∀ x y → CA x y ⊎ CA u x → (C x y ⊎ C u x) ⊎ A x ⊎ A u))
          g
          (af#-⇒
            (sup g)
            (af-sup# g sb)
            ((λ x y r → map⊎ inj₁ inj₁ (cb⇒⊎ x y r))
            ∶ (∀ x y → CB x y → (C x y ⊎ C u x) ⊎ B x ⊎ A u)))
          (λ x y r → r))
        ((λ x y → [ [ inj₁ ∘ inj₁ ∘ inj₁ , inj₁ ∘ inj₂ ]′ , pqarbr ∘ inj₂ ]′)
          ∶ (∀ x y → (C x y ⊎ C u x) ⊎ (A x ⊎ A u) × (B x ⊎ A u) →
                      ((C x y ⊎ A x × B x) ⊎ C u x) ⊎ A u))

    helper-b : ∀ u →
      Almost-full (λ x y → ((C x y ⊎ A x × B x) ⊎ C u x) ⊎ B u)
    helper-b u =
      af-⇒
        (oplus-unary
          (af-sup sa)
          ((λ x y → map⊎ inj₁ inj₁ ∘ ca⇒⊎ x y)
            ∶ (∀ x y → CA x y → (C x y ⊎ C u x) ⊎ A x ⊎ B u))
          (g u)
          (af#-⇒
            (g u) (sb u)
            ((λ x y → [ map⊎ inj₁ inj₁ ∘ cb⇒⊎ x y ,
                         map⊎ inj₂ inj₂ ∘ cb⇒⊎ u x ]′)
              ∶ (∀ x y → CB x y ⊎ CB u x → (C x y ⊎ C u x) ⊎ B x ⊎ B u)))
          (λ x y r → r))
        ((λ x y → [ [ inj₁ ∘ inj₁ ∘ inj₁ , inj₁ ∘ inj₂ ]′ , pqarbr ∘ inj₂ ]′)
          ∶ (∀ x y →
               (C x y ⊎ C u x) ⊎ (A x ⊎ B u) × (B x ⊎ B u) →
               ((C x y ⊎ A x × B x) ⊎ C u x) ⊎ B u))

-- oplus-unary-cor

oplus-unary-cor : ∀ {ℓ} {X : Set ℓ} {A B : X → Set ℓ} {C : Rel X ℓ} →
  Almost-full(λ x y → C x y ⊎ A x) →
  Almost-full(λ x y → C x y ⊎ B x) → 
  Almost-full (λ x y → C x y ⊎ (A x × B x))
oplus-unary-cor afA afB =
  oplus-unary afA (λ _ _ ca → ca)
              (wft-from-af afB) (af⇒af# afB) (λ _ _ cb → cb)

-- oplus-binary

oplus-binary : ∀ {ℓ} {X : Set ℓ} {A B : Rel X ℓ} →
  Almost-full A → Almost-full B → 
  Almost-full (λ x y → A x y × B x y)

oplus-binary-?-sup : ∀ {ℓ} {X : Set ℓ} {A B : Rel X ℓ} →
  Almost-full A → (∀ u → Almost-full (λ x y → B x y ⊎ B u x)) → 
  Almost-full (λ x y → A x y × B x y)

oplus-binary-zt-sup : ∀ {ℓ} {X : Set ℓ} {A B : Rel X ℓ} →
  (∀ x y → A x y) → (∀ u → Almost-full (λ x y → B x y ⊎ B u x)) → 
  Almost-full (λ x y → A x y × B x y)

oplus-binary-sup-sup : ∀ {ℓ} {X : Set ℓ} {A B : Rel X ℓ} → 
  (∀ u → Almost-full (λ x y → A x y ⊎ A u x)) →
  (∀ u → Almost-full (λ x y → B x y ⊎ B u x)) → 
  Almost-full (λ x y → A x y × B x y)

oplus-binary (af-zt ra) (af-zt rb)  =
  af-zt (λ x y → ra x y , rb x y)
oplus-binary (af-zt ra)  (af-sup sb) =
  oplus-binary-zt-sup ra sb
oplus-binary (af-sup sa) (af-zt rb) = af-sup (λ u →
  af-⇒ (sa u) (λ x y → map⊎ (flip _,_ (rb x y)) (flip _,_ (rb u x))))
oplus-binary (af-sup sa) (af-sup sb) =
  oplus-binary-sup-sup sa sb

oplus-binary-?-sup (af-zt ra) sb = oplus-binary-zt-sup ra sb
oplus-binary-?-sup (af-sup sa) sb = oplus-binary-sup-sup sa sb

oplus-binary-zt-sup ra sb = af-sup (λ u →
  af-⇒ (sb u) (λ x y → map⊎ (_,_ (ra x y)) (_,_ (ra u x))))

oplus-binary-sup-sup {A = A} {B = B} sa sb = af-sup (λ u → helper u)
  where
    helper : ∀ u → Almost-full (λ x y → A x y × B x y ⊎ A u x × B u x)
    helper u =
      oplus-unary-cor
        (af-⇒ (oplus-binary-?-sup (sa u) sb)
               (λ x y → λ {(p , q) → map⊎ (flip _,_ q) id p})
        ∶ Almost-full (λ x y → A x y × B x y ⊎ A u x))
        (af-⇒ (oplus-binary (af-sup sa) (sb u))
               (λ x y → λ {(q , p) → map⊎ (_,_ q) id p})
        ∶ Almost-full (λ x y → A x y × B x y ⊎ B u x))

-- af-intersection

af-intersection : ∀ {ℓ} {X : Set ℓ} {A B : Rel X ℓ} →
  Almost-full A → Almost-full B → 
  Almost-full (λ x y → A x y × B x y)
af-intersection afA afB = oplus-binary afA afB

{-***************************************************************
 *                                                              * 
 *                  Type-based constructions                    * 
 *                                                              * 
 ***************************************************************-}

------------
-- Cofmap 
------------

af-cofmap : ∀ {ℓ} {X Y : Set ℓ} (f : Y → X) {R : Rel X ℓ} →
  Almost-full R → Almost-full (λ x y → R (f x) (f y))
af-cofmap f (af-zt r) = af-zt (λ x y → r (f x) (f y))
af-cofmap f (af-sup s) = af-sup (λ z → af-cofmap f (s (f z)))

------------
-- Products
------------

-- af-product

af-product : ∀ {ℓ} {X Y : Set ℓ} → {A B : Rel X ℓ} →
  Almost-full A → Almost-full B → 
  Almost-full (λ {(x₁ , x₂) (y₁ , y₂) → A x₁ y₁ × B x₂ y₂})
af-product afA afB =
  af-intersection (af-cofmap proj₁ afA) (af-cofmap proj₂ afB)

-- af-product-left

af-product-left : ∀ {ℓ} {X Y : Set ℓ} {A : Rel X ℓ} →
  Almost-full A → 
  Almost-full (λ (x : X × Y) (y : X × Y) → A (proj₁ x) (proj₁ y))
af-product-left afA = af-cofmap proj₁ afA

--
-- Booleans
--


af-Bool : Almost-full (_≡_ {A = Bool})
af-Bool = af-sup (
  λ { true → af-sup (
        λ { true  → af-zt (λ x y → inj₂ (inj₂ refl))
          ; false → af-sup (
              λ { true  → af-zt (λ x y → inj₂ (inj₁ (inj₂ refl)))
                ; false → af-zt (λ x y → inj₂ (inj₂ (inj₁ refl)))
                })
          })
    ; false → af-sup (
        λ { true  → af-sup (
              λ { true  → af-zt (λ x y → inj₂ (inj₂ (inj₁ refl)))
                ; false → af-zt (λ x y → inj₂ (inj₁ (inj₂ refl)))
                })
          ; false → af-zt (λ x y → inj₂ (inj₂ refl))
          })
    })

--
-- Sums (through products)
--

-- sum-lift

sum-lift : ∀ {X Y : Set} (A : Rel X _) (B : Rel Y _)
  (x y : X ⊎ Y) → Set
sum-lift A B (inj₁ x₁) (inj₁ x₂) = A x₁ x₂
sum-lift A B (inj₁ x) (inj₂ y) = ⊥
sum-lift A B (inj₂ y) (inj₁ x) = ⊥
sum-lift A B (inj₂ y₁) (inj₂ y₂) = B y₁ y₂

-- left-sum-lift

left-sum-lift : {X Y : Set} (A : Rel X _) (x y : X ⊎ Y) → Set
left-sum-lift A (inj₁ x₁) (inj₁ x₂) = A x₁ x₂
left-sum-lift A (inj₁ x) (inj₂ y) = ⊥
left-sum-lift A (inj₂ y) (inj₁ x) = ⊥
left-sum-lift A (inj₂ y₁) (inj₂ y₂) = ⊤

-- af-left-sum

af-left-sum : ∀ {X Y : Set} {A : Rel X _} →
  Almost-full {X = X} A → Almost-full {X = X ⊎ Y} (left-sum-lift A)

af-left-sum {A = A} (af-zt r) =
  af-sup (λ u → af-sup (λ v → af-zt (helper u v)))
  where
    helper : ∀ u v a b → (left-sum-lift A a b ⊎ left-sum-lift A u a) ⊎
                          (left-sum-lift A v a ⊎ left-sum-lift A u v)
    helper (inj₁ ux) (inj₁ vx) a b = inj₂ (inj₂ (r ux vx))
    helper (inj₁ ux) (inj₂ vy) (inj₁ ax) b = inj₁ (inj₂ (r ux ax))
    helper (inj₁ ux) (inj₂ vy) (inj₂ ay) b = inj₂ (inj₁ tt)
    helper (inj₂ uy) (inj₁ vx) (inj₁ ax) b = inj₂ (inj₁ (r vx ax))
    helper (inj₂ uy) (inj₁ vx) (inj₂ ay) b = inj₁ (inj₂ tt)
    helper (inj₂ uy) (inj₂ vy) a b = inj₂ (inj₂ tt)

af-left-sum {X} {Y} {A} (af-sup s) =
  af-sup (λ u → helper u)
  where
    helper : ∀ u → Almost-full (λ a b → left-sum-lift A a b ⊎
                                          left-sum-lift A u a)
    helper (inj₁ ux) = af-⇒ (af-left-sum (s ux)) helper₁
      where
        helper₁ : (a b : X ⊎ Y) 
                  (r : left-sum-lift (λ x y → A x y ⊎ A ux x) a b) →
                  left-sum-lift A a b ⊎ left-sum-lift A (inj₁ ux) a
        helper₁ (inj₁ _) (inj₁ _) = λ r → r
        helper₁ (inj₁ _) (inj₂ _) = λ ()
        helper₁ (inj₂ _) (inj₁ _) = inj₁
        helper₁ (inj₂ _) (inj₂ _) = λ r → inj₁ tt

    helper (inj₂ uy) = af-sup (λ v → helper₁ v)
      where
        helper₁ : ∀ v → Almost-full
          (λ a b → (left-sum-lift A a b ⊎ left-sum-lift A (inj₂ uy) a) ⊎
                      left-sum-lift A v a ⊎ left-sum-lift A (inj₂ uy) v)
        helper₁ (inj₁ vx) = af-⇒ (af-left-sum (s vx)) helper₂
          where
            helper₂ : (a b : X ⊎ Y)
                      (r : left-sum-lift (λ x y → A x y ⊎ A vx x) a b) →
                      (left-sum-lift A a b ⊎ left-sum-lift A (inj₂ uy) a) ⊎
                       left-sum-lift A (inj₁ vx) a ⊎ ⊥
            helper₂ (inj₁ _) (inj₁ _) = [ inj₁ ∘ inj₁ , inj₂ ∘ inj₁ ]′
            helper₂ (inj₁ _) (inj₂ _) = λ ()
            helper₂ (inj₂ _) (inj₁ _) = λ ()
            helper₂ (inj₂ _) (inj₂ _) = const (inj₁ (inj₁ tt))

        helper₁ (inj₂ vy) = af-zt (λ _ b →
          [ (const (inj₂ (inj₂ tt))) , const (inj₂ (inj₂ tt)) ]′ b)

-- transpose

transpose : ∀ {ℓ} {X Y : Set ℓ} (u : X ⊎ Y) → Y ⊎ X
transpose (inj₁ x) = inj₂ x
transpose (inj₂ y) = inj₁ y

-- right-sum-lift

right-sum-lift : ∀ {X Y : Set} (B : Rel Y _) (x y : X ⊎ Y) → Set
right-sum-lift B x y = 
  left-sum-lift B (transpose x) (transpose y)

-- af-right-sum

af-right-sum : ∀ {X Y : Set} {B : Rel Y _} → 
  Almost-full {X = Y} B → Almost-full {X = X ⊎ Y} (right-sum-lift B)
af-right-sum afB =
  af-cofmap transpose (af-left-sum afB)

af-sum-lift : {X Y : Set} → (A : Rel X _) (B : Rel Y _) →
  Almost-full A → Almost-full B → Almost-full (sum-lift A B)
af-sum-lift {X} {Y} A B afA afB =
  af-⇒
    (af-intersection (af-left-sum afA) (af-right-sum afB))
    helper
  where
    helper : ∀ (a b : X ⊎ Y) x → sum-lift A B a b
    helper (inj₁ _) (inj₁ _) = proj₁
    helper (inj₁ _) (inj₂ _) = proj₁
    helper (inj₂ _) (inj₁ _) = proj₁
    helper (inj₂ _) (inj₂ _) = proj₂

--
-- Finite naturals
--

-- Finite natural values in the range [0 ... k-1] that is, k inhabitants

data Finite (k : ℕ) : Set where
  fin-intro : ∀ (x : ℕ) → (x<′k : x <′ k) → Finite k

next-fin : ∀ {k : ℕ} → Finite k → Finite k → Set
next-fin {k} (fin-intro x x<′k) (fin-intro y y<′k) =
  (suc x ≡ k) × (y ≡ 0) ⊎ (suc x <′ k) × (y ≡ suc x)

eq-fin : ∀ {k : ℕ} → Finite k → Finite k → Set
eq-fin (fin-intro x x<′k) (fin-intro y y<′k) =
  x ≡ y

lift-diag : ∀ {ℓ} {k : ℕ} {X : Set ℓ} →
              (R : Rel X ℓ) → Finite k × X → Finite k × X → Set ℓ
lift-diag R (n₁ , x₁) (n₂ , x₂) =
  (next-fin n₁ n₂) × (R x₁ x₂)

lift-pointwise : ∀ {ℓ} {k : ℕ} {X : Set ℓ} →
       (R : Rel X ℓ) → Finite k × X → Finite k × X → Set ℓ
lift-pointwise R (n₁ , x₁) (n₂ , x₂) =
  (eq-fin n₁ n₂) × (R x₁ x₂)

-- ≤′-af

_<′?_ : (x y : ℕ) → Dec (suc x ≤′ y)
x <′? y with suc x ≤? y
... | yes x<y = yes (≤⇒≤′ x<y)
... | no ¬x<y = no (λ x<′y → ¬x<y (≤′⇒≤ x<′y))

≤′-af : Almost-full _≤′_
≤′-af = af-⇒
  (af-from-wf Induction.Nat.<-well-founded _<′?_
    ∶ Almost-full (λ x y → ¬ y <′ x))
  ((λ x y ¬y<′x → ≤⇒≤′ (≤-pred (≰⇒> (λ y<x → ¬y<′x (≤⇒≤′ y<x)))))
    ∶ (∀ x y  → ¬ y <′ x → x ≤′ y))

private

  ≤′-pred : {m n : ℕ} → suc m ≤′ suc n → m ≤′ n
  ≤′-pred = ≤⇒≤′ ∘ ≤-pred ∘ ≤′⇒≤

  sk≤′k : (m n : ℕ) → suc m ≤′ m ∸ n → ⊥
  sk≤′k zero zero ()
  sk≤′k zero (suc n) ()
  sk≤′k (suc m) zero h = sk≤′k m 0 (≤′-pred h)
  sk≤′k (suc m) (suc n) h = sk≤′k m n (≤′-pred (≤′-step h))

  kxy≡ : ∀ k x → x <′ k → ∀ y → y <′ k →
           x ≤′ y → k ∸ x ≤′ k ∸ y → x ≡ y
  kxy≡ zero x () y () h1 h2
  kxy≡ (suc k′) zero x<′k zero y<′k h1 h2 = refl
  kxy≡ (suc k′) zero x<′k (suc y′) y<′k h1 h2 = ⊥-elim (sk≤′k k′ y′ h2)
  kxy≡ (suc k′) (suc x′) x<′k zero y<′k () h2
  kxy≡ (suc k′) (suc x′) x<′k (suc y′) y<′k h1 h2 =
    cong suc (kxy≡ k′ x′ (≤′-pred x<′k) y′ (≤′-pred y<′k)
                 (≤′-pred h1) h2)

af-finite : (k : ℕ) → Almost-full (eq-fin {k})
af-finite k =
  af-⇒
    ((af-intersection (af-cofmap f1 ≤′-af) (af-cofmap f2 ≤′-af))
      ∶ Almost-full (λ x y → (f1 x ≤′ f1 y) × (f2 x ≤′ f2 y)))
    ((λ {(fin-intro x x<′k) (fin-intro y y<′k) (h1 , h2) →
                    kxy≡ k x x<′k y y<′k h1 h2 })
      ∶ (∀ x y → f1 x ≤′ f1 y × f2 x ≤′ f2 y → eq-fin x y))
  where
    f1 : ∀ {k : ℕ} (fk : Finite k) → ℕ
    f1 (fin-intro x x<′k) = x

    f2 : ∀ {k : ℕ} (fk : Finite k) → ℕ
    f2 {k} (fin-intro x x<′k) = k ∸ x
