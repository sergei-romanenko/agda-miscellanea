module CoinductiveCmd where

open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.Nat
open import Data.List
open import Data.Empty

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

open import Coinduction

open ≡-Reasoning

Var = ℕ
Vars = Var → ℕ

_[_↦_] : Vars → Var → ℕ → Vars
vs [ v ↦ n ] = λ v' → if ⌊ v ≟ v' ⌋ then n else vs v' 

data Exp : Set where
  const : (n : ℕ) → Exp
  var   : (v : ℕ) → Exp
  plus  : (e1 : Exp) → (e2 : Exp) → Exp

evalExp : Vars → Exp → ℕ
evalExp vs (const n) = n
evalExp vs (var v) = vs v
evalExp vs (plus e1 e2) = evalExp vs e1 + evalExp vs e2

data Cmd : Set where
  assign : (v : Var) → (e : Exp) → Cmd
  seq    : (c1 : Cmd) → (c2 : Cmd) → Cmd
  while  : (e : Exp) → (c : Cmd) → Cmd

zero? : ℕ → Bool
zero? zero = true
zero? (suc n) = false

data EvalCmd : (vs1 : Vars) → (c : Cmd) → (vs2 : Vars) → Set where
  eAssign : ∀ {vs v e} →
    EvalCmd vs (assign v e) (vs [ v ↦ evalExp vs e ])
  eSeq : ∀ {vs1 vs2 vs3 c1 c2} →
    ∞ (EvalCmd vs1 c1 vs2) →
    ∞ (EvalCmd vs2 c2 vs3) →
    EvalCmd vs1 (seq c1 c2) vs3
  eWhileFalse : ∀ {vs e c} →
    evalExp vs e ≡ zero →
    EvalCmd vs (while e c) vs
  eWhileTrue : ∀ {vs1 vs2 vs3 e c} →
    T (not (zero? (evalExp vs1 e))) →
    ∞ (EvalCmd vs1 c vs2) →
    ∞ (EvalCmd vs2 (while e c) vs3) →
    EvalCmd vs1 (while e c) vs3

const0? : (e : Exp) → Dec (e ≡ const 0)
const0? (const zero) = yes refl
const0? (const (suc n)) = no (λ ())
const0? (var v) = no (λ ())
const0? (plus e1 e2) = no (λ ())

optExp : Exp → Exp
optExp (plus e1 e2) with const0? e1
... | yes _ = optExp e2
... | no  _ = plus (optExp e1) (optExp e2)
optExp e = e

optCmd : Cmd → Cmd
optCmd (assign v e) = assign v (optExp e)
optCmd (seq c1 c2) = seq (optCmd c1) (optCmd c2)
optCmd (while e c) = while (optExp e) (optCmd c)

optExp-correct : ∀ vs e → evalExp vs (optExp e) ≡ evalExp vs e
optExp-correct vs (const n) = refl
optExp-correct vs (var v) = refl
optExp-correct vs (plus e1 e2) with const0? e1
... | yes e1≡0 rewrite e1≡0 | optExp-correct vs e2 = refl
... | no  e1≢0 rewrite optExp-correct vs e1 | optExp-correct vs e2 = refl

optCmd-correct : ∀ {vs1 c vs2} → EvalCmd vs1 c vs2 →
                   EvalCmd vs1 (optCmd c) vs2
optCmd-correct (eAssign {vs} {v} {e}) with optExp-correct vs e
... | e-c = {!!}
optCmd-correct (eSeq t1 t2) =
  eSeq (♯ optCmd-correct (♭ t1)) (♯ optCmd-correct (♭ t2))
optCmd-correct (eWhileFalse {vs} {e} {c} z) with optExp-correct vs e
... | e-c  = {!!}
optCmd-correct (eWhileTrue nz t r) = {!!}
