{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module MergeSort3Perm {A : Set}
                      (_≤_ : A → A → Set)
                      (tot≤ : (a b : A) → a ≤ b ∨ b ≤ a)  where

open import Level hiding (suc)
open import Size
open import Data.List
open import Function
open import Algebra
open import Algebra.Structures
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Empty
open import Induction
open import Induction.Lexicographic
open import Data.Unit
open import Data.Product 
open import Data.Nat hiding (_≤?_;_⊔_;_≟_) renaming (_≤_ to _≤n_)
open import Data.Nat.Properties
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]i)

open import Permutation A
open import MergeSort3 _≤_ tot≤

forgetNp : {ι ι′ : Size} → ListN {ι} × ListN {ι′} → List A × List A
forgetNp (xs , ys) = forgetN xs , forgetN ys

lemma-deal : {ι : Size}(xs : ListN {ι}) → forgetN xs ∼p' forgetNp (deal xs)
lemma-deal []           = ∼[]r []       -- auto result
lemma-deal (x ∷ [])     = ∼[]l (x ∷ []) -- auto result
lemma-deal (x ∷ y ∷ xs) = ∼xl (∼xr (lemma-deal xs))

lemma-merge : {ι ι′ : Size}{l : Bound A}(xs : OList {ι} l)(ys : OList {ι′} l) → 
              forgetO (merge xs ys) ∼p' (forgetO xs , forgetO ys) 
lemma-merge onil l    = ∼[]r (forgetO l)
lemma-merge l    onil with l
... | onil =  ∼[]r [] -- auto result
... | (:< x {l≤x = l≤x} xs)   = ∼[]l (forgetO (:< x {l≤x = l≤x} xs))
lemma-merge (:< x {l≤x = l≤x} xs) 
            (:< y {l≤x = l≤y} ys) 
  with tot≤ x y 
... | inj₁ x≤y = ∼xl hi
    where hi = lemma-merge xs (:< y {l≤x = lexy x≤y} ys)
... | inj₂ y≤x = ∼xr hi
    where hi = lemma-merge (:< x {l≤x = lexy y≤x} xs) ys

lemma-mergeSort : {ι : Size}(xs : ListN {↑ ι}) → 
                  forgetN xs ∼ forgetO (mergeSort xs)
lemma-mergeSort []       = ∼[]                                  -- auto result
lemma-mergeSort (x ∷ []) = ∼x removeFromHead removeFromHead ∼[] -- auto result
lemma-mergeSort (x ∷ (y ∷ xs)) 
  = lemma∼p' (∼xl (∼xr (lemma-deal xs)))
             (lemma-mergeSort (x ∷ (proj₁ (deal xs))))
             (lemma-mergeSort (y ∷ (proj₂ (deal xs))))
             (lemma-merge (mergeSort (x ∷ (proj₁ (deal xs)))) (mergeSort (y ∷ (proj₂ (deal xs)))))
