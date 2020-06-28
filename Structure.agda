{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)

module Structure (funExt : Extensionality 0ℓ 0ℓ) where

open import Data.Bool as B
open import Data.Empty
open import Data.Fin as F
open import Data.List as L
import Data.List.Membership.Propositional as L
import Data.List.Relation.Unary.Any as L using (here; there)
open import Data.Nat as N
open import Data.Nat.Properties
open import Data.Sum
open import Data.Vec as V
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary

open import Utils
open import Signature

{-
Definition 3.5.3 (σ-structure).
-}
Structure : (σ : Signature) → Set
Structure σ = (p : ℕ) → (p ∈ σ) → Bool

FiniteStructure : (n : ℕ) → Set
FiniteStructure n = Structure (finite-signature n)

empty-structure : FiniteStructure 0
empty-structure = λ p ()

isContr-FiniteStructure-0 : ∀ (p : FiniteStructure 0) → p ≡ empty-structure
isContr-FiniteStructure-0 p =
  funExt (λ x → funExt (λ prf → lemma p x prf))
  where
    lemma : ∀ (p : FiniteStructure 0) x prf → p x prf ≡ empty-structure x prf
    lemma p n ()

build-fin-struct : ∀ {n} → (Fin n → Bool) → FiniteStructure n
build-fin-struct f p prf = f (fromℕ< prf)

unit-structure : Bool → FiniteStructure 1
unit-structure b 0 (s≤s z≤n) = b
unit-structure b 1 (s≤s ())

1-structure-is-true-or-false
  : (A : FiniteStructure 1)
  → A ≡ unit-structure false ⊎ A ≡ unit-structure true
1-structure-is-true-or-false A with A 0 (s≤s z≤n) B.≟ false
1-structure-is-true-or-false A | yes prf =
  inj₁ (funExt λ p → funExt (λ x → lemma p x))
  where
    lemma
      : (p : ℕ)
      → (x : suc p N.≤ 1)
      → A p x ≡ unit-structure false p x
    lemma ℕ.zero (s≤s z≤n) = prf
    lemma (suc p) (s≤s ())
1-structure-is-true-or-false A | no prf′ with ¬f→t prf′
1-structure-is-true-or-false A | no prf′ | prf =
  inj₂ (funExt λ p → funExt (λ x → lemma p x))
  where
    lemma
      : (p : ℕ)
      → (x : suc p N.≤ 1)
      → A p x ≡ unit-structure true p x
    lemma ℕ.zero (s≤s z≤n) = prf
    lemma (suc p) (s≤s ())

-- TODO: rename to strengthen-struct? or shrink-struct?
weaken-struct
  : ∀ n
  → (Structure (finite-signature (suc n)))
  → (Structure (finite-signature n))
weaken-struct n A p prf = A p (≤-step prf)

-- TODO: rename to weaken-struct?
strengthen-struct
  : ∀ n
  → Bool
  → FiniteStructure n
  → FiniteStructure (suc n)
strengthen-struct n b A p _ with p N.<? n
... | yes prf = A p prf
... | no _ = b

strengthen-struct-reduce
  : ∀ n b A p prf
  → strengthen-struct n b A p (≤-step prf) ≡ A p prf
strengthen-struct-reduce n b A p prf with p N.<? n
... | yes prf′ = cong (A p) (<-irrelevant prf′ prf)
... | no ¬prf = ⊥-elim (¬prf prf)

weaken-strengthen
  : ∀ n b A
  → weaken-struct n (strengthen-struct n b A) ≡ A
weaken-strengthen n b A = funExt λ p → funExt λ prf →
  begin
    weaken-struct n (strengthen-struct n b A) p prf
  ≡⟨⟩
    strengthen-struct n b A p (≤-step prf)
  ≡⟨ strengthen-struct-reduce n b A p prf ⟩
    A p prf
  ∎

strengthen-struct-true
  : ∀ n b A
  → strengthen-struct (suc n) b A (suc n) (s≤s (s≤s ≤-refl)) ≡ b
strengthen-struct-true n b A′ with suc n N.<? suc n
... | yes s-n<s-n = ⊥-elim (<-irrefl refl s-n<s-n)
... | no _ = refl

vec-bool→fin-struct
  : ∀ {n}
  → Vec Bool n
  → FiniteStructure n
vec-bool→fin-struct v p prf = V.lookup v (fromℕ< prf)

enum-vec-bool : ∀ n → List (Vec Bool n)
enum-vec-bool 0 = L.[ V.[] ]
enum-vec-bool (suc n) =
  L.map (true V.∷_) (enum-vec-bool n)
    L.++ L.map (false V.∷_) (enum-vec-bool n)

enum-fin-structs : ∀ n → List (FiniteStructure n)
enum-fin-structs n = L.map vec-bool→fin-struct (enum-vec-bool n)

_
  : enum-vec-bool 2
  ≡ (true  V.∷ true  V.∷ V.[]) List.∷
  (true  V.∷ false V.∷ V.[]) List.∷
  (false V.∷ true  V.∷ V.[]) List.∷
  (false V.∷ false V.∷ V.[]) List.∷ List.[]
_ = refl

{-
enum-vec-bool-complete : ∀ {n} (v : Vec Bool n) → v L.∈ enum-vec-bool n
enum-vec-bool-complete V.[] = L.here refl
enum-vec-bool-complete (false V.∷ xs) = {!!}
  where
    ind-hyp : xs L.∈ enum-vec-bool _
    ind-hyp = enum-vec-bool-complete xs
enum-vec-bool-complete (true V.∷ xs) = {!!}
-}
