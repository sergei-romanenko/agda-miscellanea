open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Maybe

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding([_])

open import Relation.Nullary.Decidable using (⌊_⌋)

open ≡-Reasoning

module StackMachine where

data binop : Set where
  Plus :  binop
  Times : binop

data exp : Set where
  Const : ℕ → exp
  Binop : binop → exp → exp → exp

B⟦_⟧ : binop → ℕ → ℕ → ℕ
B⟦ Plus ⟧  = _+_
B⟦ Times ⟧ = _*_

E⟦_⟧ : exp → ℕ
E⟦ Const n ⟧ = n
E⟦ Binop b e1 e2 ⟧ = B⟦ b ⟧ E⟦ e1 ⟧ E⟦ e2 ⟧

t01 : E⟦ Const 42 ⟧ ≡ 42
t01 = refl

t02 : E⟦ Binop Plus (Const 2) (Const 2) ⟧ ≡ 4
t02 = refl

t03 : E⟦ Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7) ⟧ ≡ 28
t03 = refl

data instr : Set where
  iConst : ℕ → instr
  iBinop : binop → instr

prog = List instr
stack = List ℕ

I⟦_⟧ : instr → stack → Maybe stack
I⟦ iConst n ⟧ s = just (n ∷ s)
I⟦ iBinop b ⟧ s with s
... | v1 ∷ v2 ∷ s' = just ((B⟦ b ⟧ v1 v2) ∷ s')
... | _ = nothing

P⟦_⟧ : prog → stack → Maybe stack
P⟦ [] ⟧ s = just s
P⟦ i ∷ p ⟧ s with I⟦ i ⟧ s
... | just s' = P⟦ p ⟧ s'
... | nothing = nothing

C⟦_⟧ : exp → prog
C⟦ Const n ⟧ = [ iConst n ]
C⟦ Binop b e1 e2 ⟧ = C⟦ e2 ⟧ ++ C⟦ e1 ⟧ ++ [ iBinop b ]

t04 : C⟦ Const 42 ⟧ ≡  [ iConst 42 ]
t04 = refl

t05 : C⟦ Binop Plus (Const 1) (Const 2) ⟧
      ≡ iConst 2 ∷ iConst 1 ∷ iBinop Plus ∷ []
t05 = refl

t06 : C⟦ Binop Times (Binop Plus (Const 1) (Const 2)) (Const 7) ⟧
      ≡ iConst 7 ∷ iConst 2 ∷ iConst 1 ∷ iBinop Plus ∷ iBinop Times ∷ []
t06 = refl

t07 : P⟦ C⟦ Const 42 ⟧ ⟧ []
      ≡ just [ 42 ]
t07 = refl

t08 : P⟦ C⟦ Binop Plus (Const 2) (Const 2) ⟧ ⟧ []
      ≡ just [ 4 ]
t08 = refl

t09 : P⟦ C⟦ Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7) ⟧ ⟧ []
      ≡ just [ 28 ]
t09 = refl

++-nil : {A : Set} → (xs : List A) →
             xs ++ [] ≡ xs

++-nil [] = refl
++-nil (x ∷ xs) =
  begin
    (x ∷ xs) ++ [] ≡⟨ refl ⟩
    x ∷ (xs ++ []) ≡⟨ cong (_∷_ x) (++-nil xs) ⟩
    x ∷ xs
  ∎

++-assoc : {A : Set} → (xs ys zs : List A) →
             (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
 begin
   ((x ∷ xs) ++ ys) ++ zs ≡⟨ refl ⟩
   (x ∷ (xs ++ ys)) ++ zs ≡⟨ refl ⟩
   x ∷ ((xs ++ ys) ++ zs) ≡⟨ cong (_∷_ x) (++-assoc xs ys zs) ⟩
   x ∷ (xs ++ (ys ++ zs)) ≡⟨ refl ⟩
   (x ∷ xs) ++ (ys ++ zs)
  ∎

C-correct' : ∀ (e : exp) → (p : prog) → (s : stack) ->
  P⟦ C⟦ e ⟧ ++ p ⟧ s ≡ P⟦ p ⟧ (E⟦ e ⟧ ∷ s)

C-correct' (Const n) p s = refl
C-correct' (Binop b e1 e2) p s =
  begin
    P⟦ C⟦ Binop b e1 e2 ⟧ ++ p ⟧ s
      ≡⟨ refl ⟩ 
    P⟦ (C⟦ e2 ⟧ ++ (C⟦ e1 ⟧ ++ [ iBinop b ])) ++ p ⟧ s
      ≡⟨ cong (λ z → P⟦ z ⟧ s)
              (++-assoc (C⟦ e2 ⟧) (C⟦ e1 ⟧ ++ [ iBinop b ] ) p) ⟩ 
    P⟦ C⟦ e2 ⟧ ++ ((C⟦ e1 ⟧ ++ [ iBinop b ]) ++ p) ⟧ s
      ≡⟨ cong (λ z → P⟦ C⟦ e2 ⟧ ++ z ⟧ s)
              (++-assoc (C⟦ e1 ⟧) [ iBinop b ] p) ⟩ 
    P⟦ C⟦ e2 ⟧ ++ (C⟦ e1 ⟧ ++ ([ iBinop b ] ++ p)) ⟧ s
      ≡⟨ refl ⟩ 
    P⟦ C⟦ e2 ⟧ ++ (C⟦ e1 ⟧ ++ (iBinop b ∷ p)) ⟧ s
      ≡⟨ C-correct' e2 (C⟦ e1 ⟧ ++ iBinop b ∷ p) s ⟩ 
    P⟦ C⟦ e1 ⟧ ++ (iBinop b ∷ p) ⟧ (E⟦ e2 ⟧ ∷ s)
      ≡⟨ C-correct' e1 (iBinop b ∷ p) (E⟦ e2 ⟧ ∷ s) ⟩ 
    P⟦ iBinop b ∷ p ⟧ (E⟦ e1 ⟧ ∷ E⟦ e2 ⟧ ∷ s)
      ≡⟨ refl ⟩ 
    P⟦ p ⟧ (B⟦ b ⟧ E⟦ e1 ⟧ E⟦ e2 ⟧ ∷ s)
      ≡⟨ refl ⟩ 
    P⟦ p ⟧ (E⟦ Binop b e1 e2 ⟧ ∷ s)
  ∎

C-correct : ∀ (e : exp) →
  P⟦ C⟦ e ⟧ ⟧ [] ≡ just [ E⟦ e ⟧ ]

C-correct e =
  begin
    P⟦ C⟦ e ⟧ ⟧ []
      ≡⟨ sym (cong (λ z → P⟦ z ⟧ []) (++-nil (C⟦ e ⟧))) ⟩
    P⟦ C⟦ e ⟧ ++ [] ⟧ []
      ≡⟨ C-correct' e [] [] ⟩
    P⟦ [] ⟧ [ E⟦ e ⟧ ]
      ≡⟨ refl ⟩
    just [ E⟦ e ⟧ ]
  ∎

--
-- Dependently-typed expressions
--

data type : Set where
  N : type
  B : type

data tbinop : type → type → type → Set where
  TPlus  : tbinop N N N
  TTimes : tbinop N N N
  TEq    : {t : type} → tbinop t t B
  TLt    : tbinop N N B


data texp : type → Set where
  TNConst : ℕ → texp N
  TBConst : Bool → texp B
  TBinop : ∀ {t1 t2 t} →
    tbinop t1 t2 t → texp t1 → texp t2 → texp t

T⟦_⟧ : type → Set
T⟦ N ⟧ = ℕ
T⟦ B ⟧ = Bool

eq-nat : ℕ → ℕ → Bool
eq-nat m n = ⌊ Data.Nat._≟_ m n ⌋

le-nat : ℕ → ℕ → Bool
le-nat m n = ⌊ Data.Nat._≤?_ m n ⌋

lt-nat : ℕ → ℕ → Bool
lt-nat m n = not (eq-nat m n) ∧ (le-nat m n)

eq-bool : Bool → Bool → Bool
eq-bool m n = ⌊ Data.Bool._≟_ m n ⌋

TB⟦_⟧ : ∀ {t1 t2 t : type} → tbinop t1 t2 t → T⟦ t1 ⟧ -> T⟦ t2 ⟧ -> T⟦ t ⟧
TB⟦ TPlus   ⟧ = _+_
TB⟦ TTimes  ⟧ = _*_
TB⟦ TEq {N} ⟧ = eq-nat
TB⟦ TEq {B} ⟧ = eq-bool
TB⟦ TLt     ⟧ = lt-nat

TE⟦_⟧ : {t : type} → texp t → T⟦ t ⟧
TE⟦ TNConst n ⟧ = n
TE⟦ TBConst b ⟧ = b
TE⟦ TBinop b e1 e2 ⟧ = TB⟦ b ⟧ TE⟦ e1 ⟧ TE⟦ e2 ⟧

u01 : TE⟦ TNConst 42 ⟧ ≡  42
u01 = refl

u02 : TE⟦ TBConst true ⟧ ≡ true
u02 = refl

u03 : TE⟦ TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7) ⟧
    ≡ 28
u03 = refl

u04 : TE⟦ TBinop TEq (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7) ⟧
  ≡ false
u04 = refl

u05 : TE⟦ TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7) ⟧
  ≡ true
u05 = refl

tstack = List type

data tinstr : tstack -> tstack -> Set where
  TiNConst : ∀ {s} → ℕ → tinstr s (N ∷ s)
  TiBConst : ∀ {s} -> Bool -> tinstr s (B ∷ s)
  TiBinop  : ∀ {arg1 arg2 res s} →
               tbinop arg1 arg2 res →
               tinstr (arg1 ∷ arg2 ∷ s) (res ∷ s)

data tprog : tstack → tstack → Set where
  []  : ∀ {s} → tprog s s
  _∷_ : ∀ {s1 s2 s3} → tinstr s1 s2 → tprog s2 s3 → tprog s1 s3

data vstack : List type → Set₁ where
  []  : vstack []
  _∷_ : ∀ {t : type} → {ts : List type} →
               (v : T⟦ t ⟧) → (vs : vstack ts)   →
               vstack (t ∷ ts)

TI⟦_⟧ : ∀ {ts ts'} →  (i : tinstr ts ts') → vstack ts -> vstack ts'
TI⟦ TiNConst n ⟧ s = n ∷ s
TI⟦ TiBConst b ⟧ s = b ∷ s
TI⟦ TiBinop b  ⟧ (v1 ∷ v2 ∷ s) = (TB⟦ b ⟧ v1 v2) ∷ s

TP⟦_⟧ : ∀ {ts ts'} → tprog ts ts' → vstack ts → vstack ts'
TP⟦ []    ⟧ s = s
TP⟦ i ∷ p ⟧ s = TP⟦ p ⟧ (TI⟦ i ⟧ s)

infixr 5 _+P+_

_+P+_ : ∀ {ts ts' ts''} → tprog ts ts' → tprog ts' ts'' → tprog ts ts''
[]      +P+ p' = p'
(i ∷ p) +P+ p' = i ∷ (p +P+ p')

TC⟦_⟧ : ∀ {t} → texp t → (ts : tstack) → tprog ts (t ∷ ts)
TC⟦ TNConst n ⟧ s = TiNConst n ∷ []
TC⟦ TBConst b ⟧ s = TiBConst b ∷ []
TC⟦ TBinop {t1} {t2} {t} b e1 e2 ⟧ s =
    TC⟦ e2 ⟧ s +P+ TC⟦ e1 ⟧ (t2 ∷ s) +P+ TiBinop b ∷ []

u06 : TP⟦ TC⟦ TNConst 42 ⟧ [] ⟧ []
      ≡ 42 ∷ []
u06 = refl

u07 : TP⟦ TC⟦ TBConst true ⟧ [] ⟧ []
      ≡ true ∷ []
u07 = refl

u08 : TP⟦ TC⟦ TBinop TTimes
                     (TBinop TPlus (TNConst 2) (TNConst 2))
                     (TNConst 7) ⟧ [] ⟧ []
      ≡ 28 ∷ []
u08 = refl

u09 : TP⟦ TC⟦ TBinop TEq (TBinop TPlus (TNConst 2) (TNConst 2))
                         (TNConst 7) ⟧ [] ⟧ []
      ≡ false ∷ []
u09 = refl

u10 : TP⟦ TC⟦ TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
                         (TNConst 7) ⟧ [] ⟧ []
      ≡ true ∷ []
u10 = refl

+P+-correct : ∀ {ts ts' ts''} → 
      (p : tprog ts ts') → (p' : tprog ts' ts'') → (s : vstack ts) →
      TP⟦ p +P+ p' ⟧ s ≡ TP⟦ p' ⟧ (TP⟦ p ⟧ s)
+P+-correct [] p' s = refl
+P+-correct (i ∷ p) p' s =
  begin
    TP⟦ (i ∷ p) +P+ p' ⟧ s
      ≡⟨ refl ⟩
    TP⟦ i ∷ (p +P+ p') ⟧ s
      ≡⟨ refl ⟩
    TP⟦ p +P+ p' ⟧ (TI⟦ i ⟧ s)
      ≡⟨ +P+-correct p p' (TI⟦ i ⟧ s) ⟩
    TP⟦ p' ⟧ (TP⟦ p ⟧ (TI⟦ i ⟧ s))
      ≡⟨ refl ⟩
    TP⟦ p' ⟧ (TP⟦ i ∷ p ⟧ s)
  ∎

TP-correct' : ∀ {t} →
  (e : texp t) →  (ts : tstack) → (s : vstack ts) →
  TP⟦ TC⟦ e ⟧ ts ⟧ s ≡ TE⟦ e ⟧ ∷ s

TP-correct' (TNConst n) ts s = refl
TP-correct' (TBConst b) ts s = refl
TP-correct' (TBinop {t1} {t2} {t} b e1 e2) ts s =
  begin
    TP⟦ TC⟦ TBinop b e1 e2 ⟧ ts ⟧ s
      ≡⟨ refl ⟩
    TP⟦ TC⟦ e2 ⟧ ts +P+ TC⟦ e1 ⟧ (t2 ∷ ts) +P+ (TiBinop b ∷ []) ⟧ s
      ≡⟨ +P+-correct (TC⟦ e2 ⟧ ts)
                     (TC⟦ e1 ⟧ (t2 ∷ ts) +P+ (TiBinop b ∷ [])) s ⟩
    TP⟦ TC⟦ e1 ⟧ (t2 ∷ ts) +P+ (TiBinop b ∷ []) ⟧ (TP⟦ TC⟦ e2 ⟧ ts ⟧ s)
      ≡⟨ cong (λ z → TP⟦ TC⟦ e1 ⟧ (t2 ∷ ts) +P+ (TiBinop b ∷ []) ⟧ z)
              (TP-correct' e2 ts s) ⟩
    TP⟦ TC⟦ e1 ⟧ (t2 ∷ ts) +P+ (TiBinop b ∷ []) ⟧ (TE⟦ e2 ⟧ ∷ s)
      ≡⟨ +P+-correct (TC⟦ e1 ⟧ (t2 ∷ ts))
                     (TiBinop b ∷ []) (TE⟦ e2 ⟧ ∷ s) ⟩
    TP⟦ TiBinop b ∷ [] ⟧ (TP⟦ TC⟦ e1 ⟧ (t2 ∷ ts) ⟧ (TE⟦ e2 ⟧ ∷ s))
      ≡⟨ (cong (λ z → TP⟦ TiBinop b ∷ [] ⟧ z)
               (TP-correct' e1 (t2 ∷ ts) (TE⟦ e2 ⟧ ∷ s)) ) ⟩
    TP⟦ TiBinop b ∷ [] ⟧ (TE⟦ e1 ⟧ ∷ (TE⟦ e2 ⟧ ∷ s))
      ≡⟨ refl ⟩
    TP⟦ [] ⟧ (TI⟦ TiBinop b ⟧ (TE⟦ e1 ⟧ ∷ TE⟦ e2 ⟧ ∷ s))
      ≡⟨ refl ⟩
    TI⟦ TiBinop b ⟧ (TE⟦ e1 ⟧ ∷ TE⟦ e2 ⟧ ∷ s)
      ≡⟨ refl ⟩
    (TB⟦ b ⟧ TE⟦ e1 ⟧ TE⟦ e2 ⟧) ∷ s
      ≡⟨ refl ⟩
    TE⟦ TBinop b e1 e2 ⟧ ∷ s
  ∎

TP-correct : ∀ {t} → (e : texp t) →
  TP⟦ TC⟦ e ⟧ [] ⟧ [] ≡ TE⟦ e ⟧ ∷ []
TP-correct e = TP-correct' e [] []
