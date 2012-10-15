module Synapse where

open import Data.Nat
open import Relation.Nullary using (¬_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Function using (_∘_)

infixr 4 _,_,_

data State : Set where
  _,_,_ : (i d v : ℕ) → State

data Synapse : State → Set where
  t1 : ∀ {i} →
     Synapse (i , 0 , 0)
  t2 : ∀ {i d v} →
     Synapse (suc i , d , v) → Synapse (i + d , 0 , suc v)
  t3 : ∀ {i d v} →
     Synapse (i , d , suc v) → Synapse (i + d + v , suc 0 , 0)
  t4 : ∀ {i d v} →
     Synapse (suc i , d , v) → Synapse (i + d + v , (suc 0), 0)

data Unsafe : State → Set where
  u1 : ∀ {x y z} →
     Unsafe (x , suc y , suc z)
  u2 : ∀ {x y z} →
     Unsafe (x , suc (suc y) , z)

data Synapse' : State → Set where
  w1 : ∀ {i} →
     Synapse' (i , suc 0 , 0)
  w2 : ∀ {i v} →
     Synapse' (i , 0 , v)

inclusion : {c : State} → Synapse c → Synapse' c
inclusion t1 = w2
inclusion (t2 p) = w2
inclusion (t3 p) = w1
inclusion (t4 p) = w1

safety : {c : State} → Synapse' c → ¬ Unsafe c
safety w1 ()
safety w2 ()

valid : {c : State} → Synapse c → ¬ Unsafe c
valid = safety ∘ inclusion

-- A direct proof that does not use Synapse'.

-- valid₁ p u = {! -c !}
-- C-c C-a

valid₁ : {c : State} → Synapse c → ¬ Unsafe c
valid₁ t1 ()
valid₁ (t2 y) ()
valid₁ (t3 y) ()
valid₁ (t4 y) ()
