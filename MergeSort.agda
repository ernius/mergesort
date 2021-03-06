{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module MergeSort {A : Set}
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

-- Section 2 

data ListN : {ι : Size} → Set where
  []  : {ι : Size} → ListN {↑ ι}
  _∷_ : {ι : Size} → A → ListN {ι} → ListN {↑ ι}

deal : {ι : Size} → ListN {ι} → ListN {ι} × ListN {ι}
deal []       = ([] , [])
deal (x ∷ []) = (x ∷ [] , []) 
deal (x ∷ y ∷ xs) with deal xs 
... | ys , zs = (x ∷ ys , y ∷ zs) 

merge : {ι ι' : Size} → ListN {ι} → ListN {ι'} → ListN
merge [] l     = l 
merge l   []   = l 
merge (x ∷ xs) (y ∷ ys)
  with tot≤ x y
... | inj₁ x≤y = x ∷ merge xs       (y ∷ ys)
... | inj₂ y≤x = y ∷ merge (x ∷ xs) ys

mergeSort : {ι : Size} → ListN {↑ ι} → ListN
mergeSort []       = []
mergeSort (x ∷ []) = x ∷ []
mergeSort (x ∷ (y ∷ xs)) with deal xs
... | (ys , zs)    = merge (mergeSort (x ∷ ys)) (mergeSort (y ∷ zs)) 

