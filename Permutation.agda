module Permutation(A : Set) where

open import Data.List 
open import Data.Product
open import Algebra
open import Algebra.Structures

data _/_⟶_ : List A → A → List A → Set where
  removeFromHead : {x : A}{xs : List A}
             -- ----------------------------------------------
                 →  (x ∷ xs) / x ⟶ xs
  removeFromTail : {x y : A}{xs ys : List A} → xs / y ⟶ ys 
            -- ------------------------------------------------------------------
                 →       (x ∷ xs) / y ⟶ (x ∷ ys)

data _∼_ : List A → List A → Set where
  ∼[] : [] ∼ []
  ∼x : {x : A}{xs ys xs' ys' : List A} → xs / x ⟶ xs' → ys / x ⟶ ys' → xs' ∼ ys' 
   -- ---------------------------------------------------------------------------------------------
     →                                xs ∼ ys

data _∼p_ : List A → List A × List A → Set where
  ∼[]r : (xs : List A) → xs ∼p ([] , xs)
  ∼[]l : (xs : List A) → xs ∼p (xs , [])
  ∼xr : {x : A}{xs ys xs' zs zs' : List A} → xs / x ⟶ xs' → zs / x ⟶ zs' → xs' ∼p (ys , zs')
   -- ---------------------------------------------------------------------------------------------
     →                                xs ∼p (ys , zs)
  ∼xl : {x : A}{xs ys xs' ys' zs : List A} → xs / x ⟶ xs' → ys / x ⟶ ys' → xs' ∼p (ys' , zs) 
   -- ---------------------------------------------------------------------------------------------
     →                                xs ∼p (ys , zs)

data _∼p'_ : List A → List A × List A → Set where
  ∼[]r : (xs : List A) → xs ∼p' ([] , xs)
  ∼[]l : (xs : List A) → xs ∼p' (xs , [])
  ∼xr : {x : A}{xs ys zs : List A} → xs ∼p' (ys , zs)
   -- -----------------------------------------------
     →          (x ∷ xs) ∼p' (ys , x ∷ zs)
  ∼xl : {x : A}{xs ys zs : List A} → xs ∼p' (ys , zs) 
   -- -----------------------------------------------
     →          (x ∷ xs) ∼p' (x ∷ ys , zs)

data ∼p'' : List A → Set where
  l[] : (xs : List A)  → ∼p'' xs
  r[] : (xs : List A)  → ∼p'' xs
  l: : (x : A)(xs : List A) → ∼p'' xs → ∼p'' (x ∷ xs) 
  r: : (x : A)(xs : List A) → ∼p'' xs → ∼p'' (x ∷ xs) 

left : {xs : List A}(p : ∼p'' xs) → List A
left (l[] xs)    = xs
left (r[] ys)    = []
left (l: x xs p) = x ∷ left p
left (r: x xs p) = left p

right : {xs : List A}(p : ∼p'' xs) → List A
right (l[] xs)    = []
right (r[] ys)    = ys
right (l: x xs p) = right p
right (r: x xs p) = x ∷ right p

-- deja de andar sized types
deal∼p : (xs : List A) → ∼p'' xs
deal∼p []           = l[] []
deal∼p (x ∷ [])     = r[] (x ∷ [])
deal∼p (x ∷ y ∷ ys) = r: x (y ∷ ys) (l: y ys (deal∼p ys))

-- merge : List A → List A → List A
-- merge [] l    = l
-- merge l  []   = l
-- merge (x ∷ xs) (y ∷ ys) with tot≤ x y
-- ... | inj₁ x≤y = x ∷ (merge xs (y ∷ ys))
-- ... | inj₂ y≤x = y ∷ (merge (x ∷ xs) ys)

lemma++/r : {y : A}{xs ys xs' : List A} → (xs / y ⟶ xs') → (xs ++ ys) / y ⟶ (xs' ++ ys)
lemma++/r removeFromHead = removeFromHead 
lemma++/r (removeFromTail xs/y⟶xs') = removeFromTail (lemma++/r xs/y⟶xs')

lemma++/l : {y : A}{xs ys ys' : List A} → (ys / y ⟶ ys') → (xs ++ ys) / y ⟶ (xs ++ ys')
lemma++/l {xs = []}     ys/y⟶ys' = ys/y⟶ys'
lemma++/l {xs = x ∷ xs} ys/y⟶ys' = removeFromTail (lemma++/l {xs = xs} ys/y⟶ys')

lemma++/ : {y : A}{xs ys : List A} → (xs ++ y ∷ ys) / y ⟶ (xs ++ ys)
lemma++/ {xs = xs} = lemma++/l {xs = xs} removeFromHead

lemma++∼l : {xs xs' ys : List A} →  xs ∼  xs' → (xs ++ ys) ∼ (xs' ++ ys)
lemma++∼l {xs} {xs'} {[]}     xs∼xs' 
  rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) xs) 
  |       ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) xs')  
  = xs∼xs'
lemma++∼l {xs} {xs'} {y ∷ ys} xs∼xs' 
  =  ∼x (lemma++/ {y} {xs} {ys})
        (lemma++/ {y} {xs'} {ys})
        (lemma++∼l xs∼xs') 

lemma++∼r : {xs ys ys' : List A} →  ys ∼  ys' → (xs ++ ys) ∼ (xs ++ ys')
lemma++∼r {xs = []}     ys∼ys' = ys∼ys'
lemma++∼r {xs = x ∷ xs} ys∼ys' 
  =  ∼x removeFromHead
        removeFromHead
        (lemma++∼r {xs = xs} ys∼ys')

refl∼ : {xs : List A} → xs ∼ xs
refl∼ {[]}     = ∼[] 
refl∼ {x ∷ xs} = ∼x removeFromHead removeFromHead (refl∼ {xs}) 

sym∼ : {xs ys : List A} → xs ∼ ys → ys ∼ xs
sym∼ ∼[]     = ∼[] 
sym∼ (∼x xs/x⟶xs' ys/x⟶ys' xs'∼ys') = 
  ∼x ys/x⟶ys' xs/x⟶xs' (sym∼ xs'∼ys')

-- ∼ transitivity
lemma// : {x y : A}{xs ys zs : List A} → xs / x ⟶ ys → ys / y ⟶ zs → ∃ (λ ws → xs / y ⟶ ws × ws / x ⟶ zs)
lemma// {x} {y} {.x ∷ .y ∷ xs} .{y ∷ xs} .{xs} removeFromHead removeFromHead 
  = x ∷ xs , 
    removeFromTail removeFromHead , 
    removeFromHead 
lemma// {x} {y} {.x ∷ .z ∷ xs} removeFromHead (removeFromTail {x = z} {ys = zs} xs/y⟶zs) 
  = x ∷ z ∷ zs , 
    removeFromTail (removeFromTail xs/y⟶zs) , 
    removeFromHead 
lemma// {x} {y} {.y ∷ xs} (removeFromTail xs/x⟶ys) removeFromHead
  = xs , 
    removeFromHead , 
    xs/x⟶ys
lemma// {x} {y} 
        (removeFromTail {x = z} xs/x⟶ys) 
        (removeFromTail ys/y⟶zs) 
  = z ∷ ws , 
    removeFromTail xs/y⟶ws , 
    removeFromTail ws/x⟶zs
  where ws = proj₁ (lemma// xs/x⟶ys ys/y⟶zs)
        xs/y⟶ws = proj₁ (proj₂ (lemma// xs/x⟶ys ys/y⟶zs))
        ws/x⟶zs = proj₂ (proj₂ (lemma// xs/x⟶ys ys/y⟶zs))

lemma∼/∷ : {x : A}{xs ys : List A} → (x ∷ xs) ∼ ys → ∃ (λ ys' → ys / x ⟶ ys' × xs ∼ ys')
lemma∼/∷ (∼x {ys' = ys'} removeFromHead ys/y⟶ys' xs'∼ys') = ys' , ys/y⟶ys' , xs'∼ys'
lemma∼/∷ (∼x (removeFromTail xs/y⟶zs) ys/y⟶ys' x∷zs∼ys') 
  = vs ,
    ys/x⟶vs ,
    ∼x xs/y⟶zs vs/y⟶us zs∼us
  where us = proj₁ (lemma∼/∷ x∷zs∼ys')
        ys'/x⟶us = proj₁ (proj₂ (lemma∼/∷  x∷zs∼ys'))
        zs∼us = proj₂ (proj₂ (lemma∼/∷  x∷zs∼ys'))
        vs = proj₁ (lemma// ys/y⟶ys' ys'/x⟶us)
        ys/x⟶vs = proj₁ (proj₂ (lemma// ys/y⟶ys' ys'/x⟶us))
        vs/y⟶us = proj₂ (proj₂ (lemma// ys/y⟶ys' ys'/x⟶us))

lemma∼/ : {x : A}{xs xs' ys : List A} → xs ∼ ys → xs / x  ⟶ xs' → ∃ (λ ys' → ys / x ⟶ ys' × xs' ∼ ys')
lemma∼/ x∷xs∼ys removeFromHead = lemma∼/∷ x∷xs∼ys
lemma∼/ x∷xs∼ys (removeFromTail xs/y⟶xs') 
  = ys' ,
    ys/y⟶ys' ,
    ∼x removeFromHead ys'/x⟶zs xs'∼zs
  where ws = proj₁ (lemma∼/∷ x∷xs∼ys)
        ys/x⟶ws = proj₁ (proj₂ (lemma∼/∷ x∷xs∼ys))
        xs∼ws = proj₂ (proj₂ (lemma∼/∷ x∷xs∼ys))
        zs = proj₁ (lemma∼/ xs∼ws xs/y⟶xs')
        ws/y⟶zs = proj₁ (proj₂ (lemma∼/ xs∼ws xs/y⟶xs'))
        xs'∼zs = proj₂ (proj₂ (lemma∼/ xs∼ws xs/y⟶xs'))
        ys' = proj₁ (lemma// ys/x⟶ws ws/y⟶zs)
        ys/y⟶ys' = proj₁ (proj₂ (lemma// ys/x⟶ws ws/y⟶zs))
        ys'/x⟶zs = proj₂ (proj₂ (lemma// ys/x⟶ws ws/y⟶zs))

trans∼ : {xs ys zs : List A} → xs ∼ ys → ys ∼ zs → xs ∼ zs
trans∼ ∼[] ∼[] = ∼[]
trans∼ ∼[] (∼x .{xs = []} () ys/x⟶ys' xs'∼ys') 
trans∼ {zs = zs} (∼x {ys = ys} xs/x⟶xs' ys/x⟶ys' xs'∼ys') ys∼zs 
  = ∼x xs/x⟶xs' zs/x⟶us (trans∼ xs'∼ys' ys'∼us)
  where zs/x⟶us = proj₁ (proj₂ (lemma∼/ ys∼zs ys/x⟶ys'))
        ys'∼us = proj₂ (proj₂ (lemma∼/ ys∼zs ys/x⟶ys'))
        us = proj₁ (lemma∼/ ys∼zs ys/x⟶ys')

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

≈-preorder : Preorder _ _ _
≈-preorder =  record { 
                Carrier = List A;
                _≈_ = _≡_;
                _∼_ = _∼_;
                isPreorder =  record {
                                  isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid (List A)) ;
                                  reflexive = reflexive-aux;
                                  trans = trans∼
                               }
                }
           where
             reflexive-aux : {i j : List A} → i ≡ j → i ∼ j
             reflexive-aux {i = i} {j = .i} refl = refl∼

import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder

lemma++∼ : {xs ys xs' ys' : List A} →  xs ∼  xs' →  ys ∼  ys' → (xs ++ ys) ∼ (xs' ++ ys')
lemma++∼ {xs} {ys} {xs'} {ys'} xs∼xs' ys∼ys' 
  = begin
     xs ++ ys
     ∼⟨ lemma++∼l xs∼xs'  ⟩
     xs' ++ ys
     ∼⟨ lemma++∼r {xs'} {ys} {ys'} ys∼ys'  ⟩
     xs' ++ ys'
    ∎

-- -- ∼p soundness
-- lemma∼p∼s : {xs ys zs : List A} → xs ∼ (ys ++ zs) → xs ∼p (ys , zs) 
-- lemma∼p∼s {[]} {[]} {[]} ∼[] = ∼[]r []
-- lemma∼p∼s {xs} {ys} {zs} (∼x x .xs .(ys ++ zs) xs' ys' xs/x⟶xs' ys++zs/x⟶ys' xs'∼ys')  = {!!}

-- ∼p correctness
lemma∼p∼ : {xs ys zs : List A} → xs ∼p (ys , zs) → xs ∼ (ys ++ zs)
lemma∼p∼ (∼[]r zs) = refl∼ 
lemma∼p∼ (∼[]l ys) 
  rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) ys) = refl∼
lemma∼p∼ (∼xr {ys = ys} xs/x⟶xs' zs/x⟶zs' xs∼ys,zs') 
  = ∼x xs/x⟶xs' (lemma++/l {xs = ys} zs/x⟶zs') (lemma∼p∼ xs∼ys,zs')
lemma∼p∼ (∼xl xs/x⟶xs' ys/x⟶ys' xs∼ys',zs) 
  = ∼x xs/x⟶xs' (lemma++/r ys/x⟶ys') (lemma∼p∼ xs∼ys',zs)

-- ∼p' correctness
lemma∼p'∼ : {xs ys zs : List A} → xs ∼p' (ys , zs) → xs ∼ (ys ++ zs)
lemma∼p'∼ (∼[]r zs) = refl∼ 
lemma∼p'∼ (∼[]l ys) 
  rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) ys) = refl∼
lemma∼p'∼ (∼xr {ys = ys} xs∼ys,zs') 
  = ∼x removeFromHead (lemma++/l {xs = ys} removeFromHead) (lemma∼p'∼ xs∼ys,zs')
lemma∼p'∼ (∼xl {x} {xs} {ys} {zs} xs∼ys',zs) 
  = ∼x removeFromHead removeFromHead  (lemma∼p'∼ xs∼ys',zs)

-- ∼p'' soundness
lemma∼p'' : {xs : List A}(p : ∼p'' xs) → xs ∼ (left p ++ right p)
lemma∼p'' (r[] ys) = refl∼
lemma∼p'' (l[] xs) 
  rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) xs) = refl∼
lemma∼p'' (r: x xs p) 
  = ∼x {x} {x ∷ xs} {left p ++ x ∷ right p} {xs} {left p ++ right p} removeFromHead (lemma++/l {x} {left p} {x ∷ right p} {right p} removeFromHead) (lemma∼p'' p)
lemma∼p'' (l: x xs p) 
  = ∼x {x} {x ∷ xs} {x ∷ left p ++ right p} {xs} {left p ++ right p} removeFromHead removeFromHead (lemma∼p'' p)

lemma∼p : {xs ys zs ws ys' zs' : List A} → xs ∼p (ys , zs) → ys ∼ ys' → zs ∼ zs' → ws ∼p (ys' , zs') → xs ∼ ws
lemma∼p {xs} {ys} {zs} {ws} {ys'} {zs'} xs∼ys,zs ys∼ys' zs∼zs' ws∼ys',zs' 
  =  begin
        xs
        ∼⟨ lemma∼p∼ xs∼ys,zs  ⟩
        ys ++ zs
        ∼⟨ lemma++∼ ys∼ys' zs∼zs'  ⟩
        ys' ++ zs'
        ∼⟨ sym∼ (lemma∼p∼ ws∼ys',zs')  ⟩
        ws
      ∎

lemma∼p' : {xs ys zs ws ys' zs' : List A} → xs ∼p' (ys , zs) → ys ∼ ys' → zs ∼ zs' → ws ∼p' (ys' , zs') → xs ∼ ws
lemma∼p' {xs} {ys} {zs} {ws} {ys'} {zs'} xs∼ys,zs ys∼ys' zs∼zs' ws∼ys',zs' 
  =  begin
        xs
        ∼⟨ lemma∼p'∼ xs∼ys,zs  ⟩
        ys ++ zs
        ∼⟨ lemma++∼ ys∼ys' zs∼zs'  ⟩
        ys' ++ zs'
        ∼⟨ sym∼ (lemma∼p'∼ ws∼ys',zs')  ⟩
        ws
      ∎
