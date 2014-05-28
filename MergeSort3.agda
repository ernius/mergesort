{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module MergeSort3 {A : Set}
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

data Sorted :  List A → Set where
  nils : Sorted []
  singls : (x : A) 
      -- -----------
         → Sorted [ x ]
  conss : (x y : A)(ys : List A) → x ≤ y → Sorted (y ∷ ys) 
    -- --------------------------------------------------------------
        →             Sorted (x ∷ y ∷ ys)

data Bound (A : Set) : Set where
  bot : Bound A 
  val : A → Bound A

data LeB : Bound A → Bound A → Set where
  lebx : {b : Bound A} → LeB bot b
  lexy : {a b : A} → a ≤ b → LeB (val a) (val b)

data OList : {ι : Size} → Bound A → Set where
  onil : {ι : Size}{l : Bound A} 
    -- --------------------------------
            → OList {↑ ι} l
  :< : {ι : Size}{l : Bound A}(x : A){l≤x : LeB l (val x)} → OList {ι} (val x) 
    -- -----------------------------------------------------------------------------------------------
                              → OList  {↑ ι} l

forgetO : {l : Bound A} → OList l → List A
forgetO onil = []
forgetO (:< x xs) = x ∷ forgetO xs

lemma-sort : {l : Bound A}(xs : OList l) → Sorted (forgetO xs)
lemma-sort onil        = nils
lemma-sort (:< x onil) = singls x
lemma-sort (:< x (:< y {lexy x≤y} xs)) 
  = conss x y (forgetO xs) x≤y (lemma-sort (:< y {lexy x≤y} xs))

data ListN : {ι : Size} → Set where
  []  : {ι : Size} → ListN {↑ ι}
  _∷_ : {ι : Size} → A → ListN {ι} → ListN {↑ ι}

forgetN : ListN → List A
forgetN [] = []
forgetN (x ∷ xs) = x ∷ forgetN xs

deal : {ι : Size}(xs : ListN {ι}) → ListN {ι} × ListN {ι}
deal []            = ([] , [])
deal (x ∷ [])     = (x ∷ [] , []) 
deal (x ∷ y ∷ xs) with deal xs 
... | ys , zs = (x ∷ ys , y ∷ zs) 

merge : {ι ι′ : Size}{l : Bound A} → OList {ι} l → OList {ι′} l → OList l
merge onil l    = l
merge l    onil = l
merge (:< x {l≤x = l≤x} xs) 
      (:< y {l≤x = l≤y} ys) 
  with tot≤ x y
... | inj₁ x≤y = (:< x {l≤x = l≤x} (merge xs (:< y {l≤x = lexy x≤y} ys)))
... | inj₂ y≤x = (:< y {l≤x = l≤y} (merge (:< x {l≤x = lexy y≤x} xs) ys))

mergeSort : {ι : Size} → ListN {↑ ι} → OList bot
mergeSort []       = onil 
mergeSort (x ∷ []) = :< x {l≤x = lebx} onil
mergeSort (x ∷ (y ∷ xs)) with deal xs
... | (ys , zs) = merge (mergeSort (x ∷ ys)) (mergeSort (y ∷ zs))

-- Verify Correctness against Sorted specification
lemma-mergeSort-sorted : (xs : ListN) → Sorted (forgetO (mergeSort xs))
lemma-mergeSort-sorted = lemma-sort ∘ mergeSort


