open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Coinduction

module CoinductiveCmd where

Var = ℕ
Vars = Var → ℕ

_[_↦_] : Vars → Var → ℕ → Vars
vs [ v ↦ n ] = λ v' → if ⌊ v ≟ v' ⌋ then n else vs v' 

data Exp : Set where
  const : ℕ → Exp
  var   : ℕ → Exp
  plus  : Exp → Exp → Exp

evalExp : Vars → Exp → ℕ
evalExp vs (const n) = n
evalExp vs (var v) = vs v
evalExp vs (plus e1 e2) = evalExp vs e1 + evalExp vs e2

data Cmd : Set where
  assign : Var → Exp → Cmd
  seq : Cmd → Cmd → Cmd
  while : Exp → Cmd → Cmd

zero? : ℕ → Bool
zero? zero = true
zero? (suc n) = false

data EvalCmd : Vars → Cmd → Vars → Set where
  eAssign : ∀ {vs v e} →
    EvalCmd vs (assign v e) (vs [ v ↦ evalExp vs e ])
  eSeq : ∀ {vs1 vs2 vs3 c1 c2} →
    EvalCmd vs1 c1 vs2 →
    EvalCmd vs2 c2 vs3 →
    EvalCmd vs1 (seq c1 c2) vs3
  eWhileFalse : ∀ {vs e c} →
    T (zero? (evalExp vs e)) →
    EvalCmd vs (while e c) vs
  eWhileTrue : ∀ {vs1 vs2 vs3 e c} →
    T (not (zero? (evalExp vs1 e))) →
    EvalCmd vs1 c vs2 →
    EvalCmd vs2 (while e c) vs3 →
    EvalCmd vs1 (while e c) vs3

