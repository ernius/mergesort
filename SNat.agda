{-# OPTIONS --sized-types #-}
module SNat where

open import Size
open import Data.Nat

-- Section 2 (Agda's Sized Types Mechanism)

data SNat : {ι : Size} → Set where
  zero : {ι : Size} → SNat {↑ ι}
  succ : {ι : Size} → SNat {ι} → SNat {↑ ι}

minus : {ι : Size} → SNat {ι} → ℕ → SNat {ι}
minus zero      y        = zero
minus x         zero     = x
minus (succ x)  (suc y)  = minus x y
--
div : {ι : Size} → SNat {ι} → ℕ → ℕ
div (zero)    y  = zero 
div (succ x)  y  = suc (div (minus x y) y)

