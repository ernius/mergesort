{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module MergeSort4 {A : Set}
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

data ListN : {ι : Size} → Set where
  []  : {ι : Size} → ListN {↑ ι}
  _∷_ : {ι : Size} → A → ListN {ι} → ListN {↑ ι}

forgetO : {l : Bound A} → OList l → List A
forgetO onil = []
forgetO (:< x xs) = x ∷ forgetO xs

forgetN : ListN → List A
forgetN [] = []
forgetN (x ∷ xs) = x ∷ forgetN xs

forgetNp : {ι ι′ : Size} → ListN {ι} × ListN {ι′} → List A × List A
forgetNp (xs , ys) = forgetN xs , forgetN ys

deal : {ι : Size}(xs : ListN {ι}) → Σ (ListN {ι} × ListN {ι}) (λ p → forgetN xs ∼p' forgetNp p)
deal []           = ([] , []) , ∼[]r []
deal (x ∷ [])     = (x ∷ [] , []) , ∼[]l (x ∷ [])
deal (x ∷ y ∷ xs) with deal xs
... | (ys , zs) , xs∼ys,zs = (x ∷ ys , y ∷ zs) , ∼xl (∼xr xs∼ys,zs)

merge : {ι ι′ : Size}{l : Bound A}(xs : OList {ι} l)(ys : OList {ι′} l) → Σ (OList l) (λ zs → forgetO zs ∼p' (forgetO xs , forgetO ys)) 
merge onil l    = l , ∼[]r (forgetO l)
merge l    onil = l , ∼[]l (forgetO l)
merge (:< x {l≤x = l≤x} xs) 
      (:< y {l≤x = l≤y} ys) 
  with tot≤ x y 
... | inj₁ x≤y = (:< x {l≤x = l≤x} zs) ,
                 ∼xl hi
    where zs = proj₁ (merge xs (:< y {l≤x = lexy x≤y} ys))
          hi = proj₂ (merge xs (:< y {l≤x = lexy x≤y} ys))
... | inj₂ y≤x = (:< y {l≤x = l≤y} ws) ,                    
                 ∼xr hi
    where ws = proj₁ (merge (:< x {l≤x = lexy y≤x} xs) ys)
          hi = proj₂ (merge (:< x {l≤x = lexy y≤x} xs) ys)

mergeSort : {ι : Size}(xs : ListN {↑ ι}) → 
            Σ (OList bot) (λ ys → forgetN xs ∼ forgetO ys)
mergeSort []       = onil , ∼[]
mergeSort (x ∷ []) 
  = :< {l = bot} x {l≤x = lebx} onil , 
    ∼x removeFromHead removeFromHead ∼[] -- auto result
mergeSort (x ∷ (y ∷ xs)) with deal xs
... | (ys , zs) , xs∼ys,zs 
  with mergeSort (x ∷ ys) | mergeSort (y ∷ zs)
... | ys' , x∷ys∼ys' | zs' , y∷zs∼zs'
  with merge ys' zs'
... | ws , ws∼ys',zs'
  = ws ,
    lemma∼p' (∼xl (∼xr (xs∼ys,zs)))
             x∷ys∼ys'
             y∷zs∼zs'
             ws∼ys',zs'

data Sorted :  List A → Set where
  nils : Sorted []
  singls : (x : A) 
      -- -----------
         → Sorted [ x ]
  conss : (x y : A)(ys : List A) → x ≤ y → Sorted (y ∷ ys) 
    -- --------------------------------------------------------------
        →             Sorted (x ∷ y ∷ ys)

lemma-sort : {l : Bound A}(xs : OList l) → Sorted (forgetO xs)
lemma-sort onil = nils
lemma-sort (:< x onil) = singls x
lemma-sort (:< x (:< y {lexy x≤y} xs)) 
  = conss x y (forgetO xs) x≤y (lemma-sort (:< y {lexy x≤y} xs))

-- Verify Correctness against Sorted specification
lemma-mergeSort-sorted : (xs : ListN) → Sorted (forgetO (proj₁ (mergeSort xs)))
lemma-mergeSort-sorted = lemma-sort ∘ proj₁ ∘ mergeSort
