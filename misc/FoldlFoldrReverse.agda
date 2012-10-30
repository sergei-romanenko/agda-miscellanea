module FoldlFoldrReverse where

open import Data.List

open import Data.List.Properties
open import Data.List.Reverse

open import Level
open import Function

open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

open ≡-Reasoning

revrev-id : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
revrev-id [] = refl
revrev-id (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
      ≡⟨ cong reverse (unfold-reverse x xs) ⟩
    reverse (reverse xs ++ [ x ]) ≡⟨ refl ⟩
    reverse (reverse xs ++ reverse [ x ])
      ≡⟨ reverse-++-commute (reverse xs) [ x ] ⟩
    reverse (reverse [ x ]) ++ reverse (reverse xs)
      ≡⟨ cong (_∷_ x) (revrev-id xs) ⟩
    x ∷ xs
  ∎

foldl→foldr : ∀ {A B : Set} (f : B → A → B) → ∀ n xs →
                foldl f n xs ≡ foldr (λ b g x → g (f x b)) id xs n
foldl→foldr f n [] = refl
foldl→foldr f n (b ∷ xs) =
  begin
    foldl f (f n b) xs
      ≡⟨ foldl→foldr f (f n b) xs ⟩
    foldr (λ b g x → g (f x b)) id xs (f n b)
      ≡⟨ refl ⟩
    foldr (λ b g x → g (f x b)) id (b ∷ xs) n
  ∎

foldr-++r : ∀ {A B : Set} (f : A → B → B) → ∀ n xs x →
          foldr f n (xs ++ [ x ]) ≡ foldr f (f x n) xs
foldr-++r f n [] x = refl
foldr-++r f n (x' ∷ xs) x = cong (f x') (foldr-++r f n xs x)

foldl→foldr-rev : ∀ {A B : Set} (f : B → A → B) → ∀ n xs →
                    foldl f n xs ≡ foldr (flip f) n (reverse xs)
foldl→foldr-rev f n [] = refl
foldl→foldr-rev f n (x ∷ xs) =
  begin
    foldl f n (x ∷ xs)
      ≡⟨ refl ⟩
    foldl f (f n x) xs
      ≡⟨ foldl→foldr-rev f (f n x) xs ⟩
    foldr (flip f) ((flip f) x n) (reverse xs)
      ≡⟨ sym (foldr-++r (flip f) n (reverse xs) x) ⟩
    foldr (flip f) n (reverse xs ++ [ x ])
      ≡⟨ cong (λ e → foldr (flip f) n e) (sym (unfold-reverse x xs)) ⟩
    foldr (flip f) n (reverse (x ∷ xs))
  ∎
