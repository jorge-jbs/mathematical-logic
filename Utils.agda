{-# OPTIONS --without-K --safe #-}

module Utils where

open import Data.Bool
open import Data.Empty
open import Data.List as L
import Data.List.Relation.Unary.Any as L using (here; there)
import Data.List.Membership.Propositional as L
open import Data.Sum
open import Relation.Binary.PropositionalEquality

¬t→f : ∀ {b : Bool} → b ≢ true → b ≡ false
¬t→f {true} prf = ⊥-elim (prf refl)
¬t→f {false} _ = refl

¬f→t : ∀ {b : Bool} → b ≢ false → b ≡ true
¬f→t {false} prf = ⊥-elim (prf refl)
¬f→t {true} _ = refl

{-
in-concat-comm
  : ∀ {A : Set} {x : A} {ys zs : List A}
  → x L.∈ zs L.++ ys
  → x L.∈ ys L.++ zs
in-concat-comm {ys = List.[]} {zs} prf = {!!}
in-concat-comm {ys = y List.∷ ys} {zs} prf = {!!}

in-concat
  : ∀ {A : Set} {x : A} {ys zs : List A}
  → (x L.∈ ys) ⊎ (x L.∈ zs)
  → x L.∈ (ys L.++ zs)
in-concat {ys = .(_ List.∷ _)} {zs} (inj₁ (L.here prf)) rewrite prf =
  L.here refl
in-concat {ys = .(_ List.∷ _)} {zs} (inj₁ (L.there prf)) =
  L.there (in-concat (inj₁ prf))
in-concat {x = x} {ys = ys} {zs = zs} (inj₂ prf) = in-concat-comm {ys = ys} ind-hyp
  where
    ind-hyp : x L.∈ zs L.++ ys
    ind-hyp = in-concat {ys = zs} {zs = ys} (inj₁ prf)
-}
