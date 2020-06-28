{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)

module Table (funExt : Extensionality 0ℓ 0ℓ) where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Signature
open import Structure funExt

data Table : ℕ → Set where
  constant : (b : Bool) → Table 0
  branch
    : ∀ {n}
    → (t₁ : Table n)
    -- ^ true branch
    → (t₂ : Table n)
    -- ^ false branch
    → Table (suc n)

_ : Table 2
_ =
  branch
    (branch  -- T
      (constant false)  -- T T
      (constant false)  -- T F
    )
    (branch  -- F
      (constant false)  -- F T
      (constant false)  -- F F
    )

weaken-struct-fun
  : ∀ n
  → (FiniteStructure (suc n) → Bool)
  → Bool
  → (FiniteStructure n → Bool)
weaken-struct-fun n f b A′ = f (strengthen-struct n b A′)

table→fun
  : ∀ {n}
  → Table n
  → (FiniteStructure n → Bool)
table→fun {0} (constant b) A′ = b
table→fun {suc n} (branch t₁ t₂) A with A n (s≤s ≤-refl)
... | true = table→fun t₁ (weaken-struct _ A)
... | false = table→fun t₂ (weaken-struct _ A)

fun→table
  : ∀ {n}
  → (Structure (finite-signature n) → Bool)
  → Table n
fun→table {0} g = constant (g empty-structure)
fun→table {suc _} g =
  branch
    (fun→table (weaken-struct-fun _ g true))
    (fun→table (weaken-struct-fun _ g false))

table→fun-vec
  : ∀ {n}
  → Table n
  → (Vec Bool n → Bool)
table→fun-vec (constant b) Vec.[] = b
table→fun-vec (branch t₁ t₂) (true Vec.∷ v) = table→fun-vec t₁ v
table→fun-vec (branch t₁ t₂) (false Vec.∷ v) = table→fun-vec t₂ v

fun-vec→table
  : ∀ {n}
  → (Vec Bool n → Bool)
  → Table n
fun-vec→table {0} f = constant (f Vec.[])
fun-vec→table {suc n} f =
  branch
    (fun-vec→table (λ v → f (true Vec.∷ v)))
    (fun-vec→table (λ v → f (false Vec.∷ v)))

fun-vec→table→fun-vec
  : ∀ {n} (f : Vec Bool n → Bool)
  → table→fun-vec (fun-vec→table f) ≡ f
fun-vec→table→fun-vec f = funExt (lemma f)
  where
    lemma
      : ∀ {n} (f : Vec Bool n → Bool) (v : Vec Bool n)
      → table→fun-vec (fun-vec→table f) v ≡ f v
    lemma f Vec.[] = refl
    lemma f (true Vec.∷ v) = lemma (λ v₁ → f (true Vec.∷ v₁)) v
    lemma f (false Vec.∷ v) = lemma (λ v₁ → f (false Vec.∷ v₁)) v

table→fun-vec→table
  : ∀ {n} (t : Table n)
  → fun-vec→table (table→fun-vec t) ≡ t
table→fun-vec→table (constant x) = refl
table→fun-vec→table (branch t₁ t₂) = cong₂ branch ind-hyp₁ ind-hyp₂
  where
    ind-hyp₁ : fun-vec→table (table→fun-vec t₁) ≡ t₁
    ind-hyp₁ = table→fun-vec→table t₁

    ind-hyp₂ : fun-vec→table (table→fun-vec t₂) ≡ t₂
    ind-hyp₂ = table→fun-vec→table t₂


