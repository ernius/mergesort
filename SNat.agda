{-# OPTIONS --sized-types #-}
module SNat where

open import Size

-- Section 2 (Agda's Sized Types Mechanism)

data SNat : {ι : Size} → Set where
  zero : {ι : Size} → SNat {↑ ι}
  succ : {ι : Size} → SNat {ι} → SNat {↑ ι}

minus : {ι : Size} → SNat {ι} → SNat → SNat {ι}
minus zero     y        = zero
minus x        zero     = x
minus (succ x) (succ y) = minus x y

div : {ι : Size} → SNat {ι} → SNat → SNat {ι}
div (zero)   y = zero 
div (succ x) y = succ (div (minus x y) y)

