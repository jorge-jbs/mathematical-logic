{-# OPTIONS --without-K --safe #-}

module Utils where

open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality

¬t→f : ∀ {b : Bool} → b ≢ true → b ≡ false
¬t→f {true} prf = ⊥-elim (prf refl)
¬t→f {false} _ = refl

¬f→t : ∀ {b : Bool} → b ≢ false → b ≡ true
¬f→t {false} prf = ⊥-elim (prf refl)
¬f→t {true} _ = refl
