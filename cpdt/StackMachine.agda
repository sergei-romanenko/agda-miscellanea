open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Data.Maybe

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)

open import Relation.Nullary using (¬_)
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

binopDenote : binop → ℕ → ℕ → ℕ
binopDenote Plus  = _+_
binopDenote Times = _*_

expDenote : exp → ℕ
expDenote (Const n) = n
expDenote (Binop b e1 e2) = (binopDenote b) (expDenote e1) (expDenote e2)

t01 : expDenote (Const 42) ≡ 42
t01 = refl

t02 : expDenote (Binop Plus (Const 2) (Const 2)) ≡ 4
t02 = refl

t03 : expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)) ≡ 28
t03 = refl

data instr : Set where
  iConst : ℕ → instr
  iBinop : binop → instr

prog = List instr
stack = List ℕ

instrDenote : instr → stack → Maybe stack
instrDenote (iConst n) s = just (n ∷ s)
instrDenote (iBinop b) s with s
... | arg1 ∷ arg2 ∷ s' = just ((binopDenote b arg1 arg2) ∷ s')
... | _ = nothing

progDenote : prog → stack → Maybe stack
progDenote [] s = just s
progDenote (i ∷ p) s with instrDenote i s
... | just s' = progDenote p s'
... | nothing = nothing

compile : exp → prog
compile (Const n) = [ iConst n ]
compile (Binop b e1 e2) = compile e2 ++ compile e1 ++ [ iBinop b ]

t04 : compile (Const 42) ≡  [ iConst 42 ]
t04 = refl

t05 : compile (Binop Plus (Const 1) (Const 2))
      ≡ iConst 2 ∷ iConst 1 ∷ iBinop Plus ∷ []
t05 = refl

t06 : compile (Binop Times (Binop Plus (Const 1) (Const 2)) (Const 7))
      ≡ iConst 7 ∷ iConst 2 ∷ iConst 1 ∷ iBinop Plus ∷ iBinop Times ∷ []
t06 = refl

t07 : progDenote (compile (Const 42)) []
      ≡ just [ 42 ]
t07 = refl

t08 : progDenote (compile (Binop Plus (Const 2) (Const 2))) []
      ≡ just [ 4 ]
t08 = refl

t09 : progDenote (compile 
     (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) []
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

compile-correct' : ∀ (e : exp) → (p : prog) → (s : stack) ->
  progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)

compile-correct' (Const n) p s = refl
compile-correct' (Binop b e1 e2) p s =
  begin
    progDenote (compile (Binop b e1 e2) ++ p) s
      ≡⟨ refl ⟩ 
    progDenote ((compile e2 ++ (compile e1 ++ [ iBinop b ])) ++ p) s
      ≡⟨ cong (λ z → progDenote z s)
           (++-assoc (compile e2) (compile e1 ++ [ iBinop b ] ) p) ⟩ 
    progDenote (compile e2 ++ ((compile e1 ++ [ iBinop b ]) ++ p)) s
      ≡⟨ cong (λ z → progDenote (compile e2 ++ z) s)
           (++-assoc (compile e1) [ iBinop b ] p) ⟩ 
    progDenote (compile e2 ++ (compile e1 ++ ([ iBinop b ] ++ p))) s
      ≡⟨ refl ⟩ 
    progDenote (compile e2 ++ (compile e1 ++ ( iBinop b ∷ p))) s
      ≡⟨ compile-correct' e2 (compile e1 ++ iBinop b ∷ p) s ⟩ 
    progDenote (compile e1 ++ iBinop b ∷ p) (expDenote e2 ∷ s)
      ≡⟨ compile-correct' e1 (iBinop b ∷ p) (expDenote e2 ∷ s) ⟩ 
    progDenote (iBinop b ∷ p) (expDenote e1 ∷ expDenote e2 ∷ s)
      ≡⟨ refl ⟩ 
    progDenote p (binopDenote b (expDenote e1) (expDenote e2) ∷ s)
      ≡⟨ refl ⟩ 
    progDenote p (expDenote (Binop b e1 e2) ∷ s)
  ∎

compile-correct : ∀ (e : exp) →
  progDenote (compile e) [] ≡ just ([ expDenote e ])

compile-correct e =
  begin
    progDenote (compile e) []
      ≡⟨ sym (cong (λ z → progDenote z []) (++-nil (compile e))) ⟩
    progDenote (compile e ++ []) []
      ≡⟨ compile-correct' e [] [] ⟩
    progDenote [] [ expDenote e ]
      ≡⟨ refl ⟩
    just ([ expDenote e ])
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

typeDenote : type → Set
typeDenote N = ℕ
typeDenote B = Bool

eq-nat : ℕ → ℕ → Bool
eq-nat m n = ⌊ Data.Nat._≟_ m n ⌋

le-nat : ℕ → ℕ → Bool
le-nat m n = ⌊ Data.Nat._≤?_ m n ⌋

lt-nat : ℕ → ℕ → Bool
lt-nat m n = not (eq-nat m n) ∧ (le-nat m n)

eq-bool : Bool → Bool → Bool
eq-bool m n = ⌊ Data.Bool._≟_ m n ⌋

tbinopDenote : ∀ {t1 t2 t : type} → tbinop t1 t2 t →
                 typeDenote t1 -> typeDenote t2 -> typeDenote t
tbinopDenote TPlus = _+_
tbinopDenote TTimes = _*_
tbinopDenote (TEq {N}) = eq-nat
tbinopDenote (TEq {B}) = eq-bool
tbinopDenote TLt = lt-nat

texpDenote : {t : type} → texp t → typeDenote t
texpDenote (TNConst n) = n
texpDenote (TBConst b) = b
texpDenote (TBinop b e1 e2) =
  (tbinopDenote b) (texpDenote e1) (texpDenote e2)

u01 : texpDenote (TNConst 42) ≡  42
u01 = refl

u02 : texpDenote (TBConst true) ≡ true
u02 = refl

u03 : texpDenote
    (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
    ≡ 28
u03 = refl

u04 : texpDenote
  (TBinop TEq (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7))
  ≡ false
u04 = refl

u05 : texpDenote
  (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
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
  TNil :  ∀ {s} → tprog s s
  TCons : ∀ {s1 s2 s3} →
            tinstr s1 s2 →
            tprog s2 s3 →
            tprog s1 s3

data vstack : List type → Set₁ where
  []  : vstack []
  _∷_ : ∀ {t : type} → {ts : List type} →
               (v : typeDenote t) → (vs : vstack ts)   →
               vstack (t ∷ ts)

tinstrDenote : ∀ {ts ts'} →  (i : tinstr ts ts') → vstack ts -> vstack ts'
tinstrDenote (TiNConst n) s = n ∷ s
tinstrDenote (TiBConst b) s = b ∷ s
tinstrDenote (TiBinop b) (v1 ∷ v2 ∷ s) = ((tbinopDenote b) v1 v2) ∷ s

tprogDenote : ∀ {ts ts'} → tprog ts ts' → vstack ts → vstack ts'
tprogDenote TNil = λ s → s
tprogDenote (TCons i p) = λ s → tprogDenote p (tinstrDenote i s)

tconcat : ∀ {ts ts' ts''} → tprog ts ts' → tprog ts' ts'' → tprog ts ts''
tconcat TNil = λ p' → p'
tconcat (TCons i p) = λ p' → TCons i (tconcat p p')

tcompile : ∀ {t} → texp t → (ts : tstack) → tprog ts (t ∷ ts)
tcompile (TNConst n) s = TCons (TiNConst n) TNil
tcompile (TBConst b) s = TCons (TiBConst b) TNil
tcompile (TBinop {t1} {t2} {t} b e1 e2) s =
           (tconcat (tcompile e2 s)
           (tconcat (tcompile e1 (t2 ∷ s))
           (TCons (TiBinop b) TNil)))

u06 : tprogDenote (tcompile (TNConst 42) []) []
      ≡ 42 ∷ []
u06 = refl

u07 : tprogDenote (tcompile (TBConst true) []) []
      ≡ true ∷ []
u07 = refl

u08 : tprogDenote (tcompile
      (TBinop TTimes (TBinop TPlus (TNConst 2)
      (TNConst 2)) (TNConst 7)) []) []
      ≡ 28 ∷ []
u08 = refl

u09 : tprogDenote
      (tcompile (TBinop TEq (TBinop TPlus (TNConst 2)
      (TNConst 2)) (TNConst 7)) []) []
      ≡ false ∷ []
u09 = refl

u10 : tprogDenote
      (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
      (TNConst 7)) []) []
      ≡ true ∷ []
u10 = refl

tconcat-correct : ∀ {ts ts' ts''} → 
      (p : tprog ts ts') → (p' : tprog ts' ts'') → (s : vstack ts) →
      tprogDenote (tconcat p p') s ≡ tprogDenote p' (tprogDenote p s)
tconcat-correct TNil p' s = refl
tconcat-correct (TCons i p) p' s =
  begin
    tprogDenote (tconcat (TCons i p) p') s
      ≡⟨ refl ⟩
    tprogDenote (TCons i (tconcat p p')) s
      ≡⟨ refl ⟩
    tprogDenote (tconcat p p') (tinstrDenote i s)
      ≡⟨ tconcat-correct p p' (tinstrDenote i s) ⟩
    tprogDenote p' (tprogDenote p (tinstrDenote i s))
      ≡⟨ refl ⟩
    tprogDenote p' (tprogDenote (TCons i p) s)
  ∎

tcompile-correct' : ∀ {t} →
  (e : texp t) →  (ts : tstack) → (s : vstack ts) →
  tprogDenote (tcompile e ts) s ≡ (texpDenote e ∷ s)

tcompile-correct' (TNConst n) ts s = refl
tcompile-correct' (TBConst b) ts s = refl
tcompile-correct' (TBinop {t1} {t2} {t} b e1 e2) ts s =
  begin
    tprogDenote (tcompile (TBinop b e1 e2) ts) s
      ≡⟨ refl ⟩
    tprogDenote (tconcat (tcompile e2 ts)
                (tconcat (tcompile e1 (t2 ∷ ts))
                         (TCons (TiBinop b) TNil))) s
      ≡⟨ tconcat-correct (tcompile e2 ts)
                         (tconcat (tcompile e1 (t2 ∷ ts))
                                  (TCons (TiBinop b) TNil)) s ⟩
    tprogDenote (tconcat (tcompile e1 (t2 ∷ ts))
                         (TCons (TiBinop b) TNil))
                (tprogDenote (tcompile e2 ts) s)
      ≡⟨ cong (λ z →
              tprogDenote (tconcat (tcompile e1 (t2 ∷ ts))
                          (TCons (TiBinop b) TNil)) z)
              (tcompile-correct' e2 ts s) ⟩
    tprogDenote (tconcat (tcompile e1 (t2 ∷ ts))
                         (TCons  (TiBinop b) TNil))
                (texpDenote e2 ∷ s)
      ≡⟨ tconcat-correct (tcompile e1 (t2 ∷ ts))
                         (TCons (TiBinop b) TNil)
                         (texpDenote e2 ∷ s) ⟩
    tprogDenote (TCons  (TiBinop b) TNil)
                (tprogDenote (tcompile e1 (t2 ∷ ts)) (texpDenote e2 ∷ s))
      ≡⟨ (cong (λ z → tprogDenote (TCons (TiBinop b) TNil) z)
               (tcompile-correct' e1 (t2 ∷ ts) (texpDenote e2 ∷ s)) ) ⟩
    tprogDenote (TCons (TiBinop b) TNil)
                 (texpDenote{t1} e1 ∷ (texpDenote{t2} e2 ∷ s))

      ≡⟨ refl ⟩
    tprogDenote TNil
                (tinstrDenote (TiBinop b)
                (texpDenote e1 ∷ (texpDenote e2 ∷ s)))
      ≡⟨ refl ⟩
    tinstrDenote (TiBinop b) (texpDenote e1 ∷ (texpDenote e2 ∷ s))
      ≡⟨ refl ⟩
    ((tbinopDenote b) (texpDenote e1) (texpDenote e2)) ∷ s
      ≡⟨ refl ⟩
    texpDenote (TBinop b e1 e2) ∷ s
  ∎

tcompile_correct : ∀ {t} → (e : texp t) →
  tprogDenote (tcompile e []) [] ≡ (texpDenote e ∷ [])
tcompile_correct e = tcompile-correct' e [] []
