{-
Formalization of Propositional Logic following "Mathematical Logic" of
Ian Chiswell and Wilfrid Hodges.
-}

{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ; _⊔_)
open import Axiom.Extensionality.Propositional using (Extensionality)

module PropositionalLogic (funExt : Extensionality 0ℓ 0ℓ) where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool using
  (Bool; false; true; _≟_; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Nat using (ℕ; suc; _<_; _<?_; _>_; _>?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step; <-irrefl; <-irrelevant)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,′_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Equivalence using (_⇔_; Equivalence; equivalence)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Decidable; Satisfiable; ∅; _∪_; _⊆_) renaming (｛_｝ to ⟦_⟧)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
import Relation.Binary.PropositionalEquality.Core
open Relation.Binary.PropositionalEquality.Core using (subst)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)

max : ℕ → ℕ → ℕ
max 0 m = m
max (suc n) 0 = suc n
max (suc n) (suc m) = max n m

Signature : Set₁
Signature = Pred ℕ 0ℓ

FiniteSignature : ℕ → Signature
FiniteSignature n = λ k → k < n

_∈_ : (p : ℕ) (σ : Signature) → Set
p ∈ σ = σ p

data LP : (σ : Signature) → Set₁ where
  ⊥′ : ∀ {σ} → LP σ
  var : ∀ {σ} → (p : ℕ) → p ∈ σ → LP σ
  ¬′_ : ∀ {σ} → LP σ → LP σ
  _∧′_ _∨′_ _→′_ _↔′_ : ∀ {σ} → LP σ → LP σ → LP σ

height : ∀ {σ} → LP σ → ℕ
height ⊥′ = 0
height (var p _) = 0
height (¬′ ψ) = suc (height ψ)
height (ϕ ∧′ ψ) = max (height ϕ) (height ψ)
height (ϕ ∨′ ψ) = max (height ϕ) (height ψ)
height (ϕ →′ ψ) = max (height ϕ) (height ψ)
height (ϕ ↔′ ψ) = max (height ϕ) (height ψ)

Assumptions : (σ : Signature) → Set₂
Assumptions σ = Pred (LP σ) (Level.suc 0ℓ)

infixr 3 _⊢_

{-
Definition 3.4.1 (σ-derivation) and 3.4.4 (σ-sequent). Merged thanks to
dependent types.
-}
data _⊢_
    : {σ : Signature}
    → (Γ : Assumptions σ)
    → (conclusion : LP σ)
    → Set₂ where
  weakening
    : ∀ {σ} {Γ Δ : Assumptions σ} {ϕ}
    → Γ ⊆ Δ
    → Γ ⊢ ϕ
    → Δ ⊢ ϕ
  A
    : ∀ {σ}
    → (ϕ : LP σ)
    → ⟦ ϕ ⟧ ⊢ ϕ
  →I
    : ∀ {σ Γ}
    → (ϕ ψ : LP σ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ ψ
    → Γ ⊢ (ϕ →′ ψ)
  ¬I
    : ∀ {σ Γ}
    → (ϕ : LP σ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ ⊥′
    → Γ ⊢ (¬′ ϕ)
  RAA
    : ∀ {σ Γ}
    → (ϕ : LP σ)
    → (Γ ∪ ⟦ ¬′ ϕ ⟧) ⊢ ⊥′
    → Γ ⊢ ϕ
  →E
    : ∀ {σ Γ} {ϕ ψ : LP σ}
    → Γ ⊢ ϕ
    → Γ ⊢ (ϕ →′ ψ)
    → Γ ⊢ ψ
  ∨E
    : ∀ {σ Γ} {ϕ ψ χ : LP σ}
    → Γ       ⊢ (ϕ ∨′ ψ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ χ
    → (Γ ∪ ⟦ ψ ⟧) ⊢ χ
    → Γ ⊢ χ
  -- TODO: add the rest of the derivation rules

example-2-4-5
  : ∀ {σ} (ϕ ψ χ : LP σ)
  → (⟦ ϕ →′ ψ ⟧ ∪ ⟦ ψ →′ χ ⟧) ⊢ (ϕ →′ χ)
example-2-4-5 ϕ ψ χ =
  →I ϕ χ  -- ϕ → χ
    (→E   -- χ
      (→E  -- ψ
        (weakening lemma₁ (A ϕ))
        (weakening lemma₂ (A (ϕ →′ ψ)))
      )
      (weakening lemma₃ (A (ψ →′ χ)))  -- ψ → χ
    )
  where
    lemma₁
      : ∀ {σ} {ϕ ψ χ : LP σ}
      → ⟦ ϕ ⟧ ⊆ ((⟦ ϕ →′ ψ ⟧ ∪ ⟦ ψ →′ χ ⟧) ∪ ⟦ ϕ ⟧)
    lemma₁ = λ z → inj₂ z

    lemma₂ : ∀ {σ} {ϕ ψ χ : LP σ} →
      _⊆_
      (⟦_⟧ (_→′_ {σ} ϕ ψ))
      (_∪_
      (_∪_
      (⟦_⟧ (_→′_ {σ} ϕ ψ))
      (⟦_⟧ (_→′_ {σ} ψ χ)))
      (⟦_⟧ ϕ))
    lemma₂ = λ z → inj₁ (inj₁ z)

    lemma₃ : ∀ {σ} {ϕ ψ χ : LP σ} →
      _⊆_ {_} {LP σ} {_} {_}
      (⟦_⟧ {_} {LP σ} (_→′_ {σ} ψ χ))
      (_∪_ {_} {LP σ} {_} {_}
      (_∪_ {_} {LP σ} {_} {_}
      (⟦_⟧ {_} {LP σ} (_→′_ {σ} ϕ ψ))
      (⟦_⟧ {_} {LP σ} (_→′_ {σ} ψ χ)))
      (⟦_⟧ {_} {LP σ} ϕ))
    lemma₃ = λ z → inj₁ (inj₂ z)

example-3-4-3
  : ∀ {σ} {Γ : Assumptions σ} {ϕ : LP σ}
  → Γ ∪ ⟦ ¬′ ϕ ⟧ ⊢ ⊥′
  → Γ ⊢ ϕ
example-3-4-3 {ϕ = ϕ} ⊢¬¬ϕ = RAA ϕ ⊢¬¬ϕ

{-
Definition 3.5.3 (σ-structure).
-}
Structure : (σ : Signature) → Set
Structure σ = (p : ℕ) → (p ∈ σ) → Bool

FiniteStructure : (n : ℕ) → Set
FiniteStructure n = Structure (FiniteSignature n)

empty-structure : FiniteStructure 0
empty-structure = λ p ()

build-fin-struct : ∀ {n} → (Fin n → Bool) → FiniteStructure n
build-fin-struct f p prf = f (fromℕ< prf)

_⇒b_ : Bool → Bool → Bool
true ⇒b true = true
true ⇒b false = false
false ⇒b true = true
false ⇒b false = true

_⇔b_ : Bool → Bool → Bool
true ⇔b true = true
false ⇔b false = true
true ⇔b false = false
false ⇔b true = false

_*_ : ∀ {σ} → Structure σ → LP σ → Bool
f * ⊥′ = false
f * var p prf = f p prf
f * (¬′ χ) = not (f * χ)
f * (χ₁ ∧′ χ₂) = (f * χ₁) ∧ (f * χ₂)
f * (χ₁ ∨′ χ₂) = (f * χ₁) ∨ (f * χ₂)
f * (χ₁ →′ χ₂) = (f * χ₁) ⇒b (f * χ₂)
f * (χ₁ ↔′ χ₂) = (f * χ₁) ⇔b (f * χ₂)

module example-3-5-4 where
  σ : Signature
  σ = λ k → k < 3

  A′ : FiniteStructure 3
  A′ = build-fin-struct
    λ
      { zero → false
      ; (suc zero) → true
      ; (suc (suc zero)) → true
      }

  χ : LP σ
  χ =
    var 1 (s≤s (s≤s z≤n))
      ∧′ (¬′ (var 0 (s≤s z≤n) →′ var 2 (s≤s (s≤s (s≤s z≤n)))))

  _ : A′ * χ ≡ false
  _ = refl

{-
Definition 3.5.7 (tautology)
-}

⊨ : ∀ {σ} (ϕ : LP σ) → Set
⊨ {σ} ϕ = ∀ {A′ : Structure σ} → A′ * ϕ ≡ true

¬t→f : ∀ {b : Bool} → b ≢ true → b ≡ false
¬t→f {true} prf = ⊥-elim (prf refl)
¬t→f {false} _ = refl

¬f→t : ∀ {b : Bool} → b ≢ false → b ≡ true
¬f→t {false} prf = ⊥-elim (prf refl)
¬f→t {true} _ = refl

{-
Lemma 3.6.1
-}

module lemma-3-6-1 {σ} (ϕ ψ : LP σ) where
  I : Set
  I = ∀ (A′ : Structure σ) → A′ * ϕ ≡ true ⇔ A′ * ψ ≡ true

  II : Set
  II = ∀ (A′ : Structure σ) → A′ * ϕ ≡ A′ * ψ

  III : Set
  III = ⊨ (ϕ ↔′ ψ)

  Lemma : Set
  Lemma = I ⇔ II × II ⇔ III

  i→ii : I → II
  i→ii i-prf A′ with A′ * ϕ ≟ true | A′ * ψ ≟ true
  i→ii i-prf A′ | yes ϕ-true | yes ψ-true
      rewrite ϕ-true | ψ-true = refl
  i→ii i-prf A′ | no ϕ-false | no ψ-false
      rewrite ¬t→f ϕ-false | ¬t→f ψ-false = refl
  i→ii i-prf A′ | no _       | yes ψ-true
      rewrite ψ-true with Equivalence.from (i-prf A′) ⟨$⟩ ψ-true
  i→ii i-prf A′ | no _       | yes ψ-true | prf = prf
  i→ii i-prf A′ | yes ϕ-true | no _
      rewrite ϕ-true with Equivalence.to (i-prf A′) ⟨$⟩ ϕ-true
  i→ii i-prf A′ | yes ϕ-true | no _       | prf = sym prf

  ii→iii : II → III
  ii→iii = {!!}

  iii→i : III → I
  iii→i = {!!}

  ii→i : II → I
  ii→i = iii→i ∘ ii→iii

  iii→ii : III → II
  iii→ii = i→ii ∘ iii→i

  proof : Lemma
  proof = equivalence i→ii ii→i ,′ equivalence ii→iii iii→ii

{-
Definition 3.6.2

In the book it is defined as `I ∨ II ∨ III` but here we define it
like this since the three propositions are equivalent and it is easier
to prove that `_~_` is an equivalence this way.
-}
_~_ : ∀ {σ} → Rel (LP σ) 0ℓ
ϕ ~ ψ = II
  where open lemma-3-6-1 ϕ ψ

{-
Theorem 3.6.4
-}
~-is-equivalence : ∀ {σ} → IsEquivalence (_~_ {σ})
~-is-equivalence {σ} =
  record
    { refl = λ A′ → refl
    ; sym = λ x~y A′ → sym (x~y A′)
    ; trans = λ x~y y~z A′ → trans (x~y A′) (y~z A′)
    }

-- TODO: maybe take a term in LP σ to a term in LP τ?

{-
Definition 3.7.1
-}

record Substitution (σ : Signature) (τ : Signature) : Set₁ where
  constructor substitution
  field
    dec : Decidable τ
    τ⊆σ : τ ⊆ σ
    subst-var : (p : ℕ) → p ∈ τ → LP σ

open Substitution

sets-lemma : ∀ {σ τ} (p : ℕ) → τ ⊆ σ → p ∈ (σ ∪ τ) → p ∈ σ
sets-lemma p τ⊆σ p∈σ∪τ with p∈σ∪τ
... | inj₁ p∈σ = p∈σ
... | inj₂ p∈τ = τ⊆σ p∈τ

weaken-term-signature : ∀ {σ τ} → LP σ → LP (σ ∪ τ)
weaken-term-signature ⊥′ = ⊥′
weaken-term-signature (var p p∈σ) = var p (inj₁ p∈σ)
weaken-term-signature (¬′ ϕ) = ¬′ weaken-term-signature ϕ
weaken-term-signature (ϕ₁ ∧′ ϕ₂) = weaken-term-signature ϕ₁ ∧′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ ∨′ ϕ₂) = weaken-term-signature ϕ₁ ∨′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ →′ ϕ₂) = weaken-term-signature ϕ₁ →′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ ↔′ ϕ₂) = weaken-term-signature ϕ₁ ↔′ weaken-term-signature ϕ₂

_[_] : ∀ {σ τ} → LP (σ ∪ τ) → Substitution σ τ → LP σ
⊥′ [ S ] = ⊥′
_[_] {σ} {τ} (var p p∈σ∪τ) S with dec S p
... | yes p∈τ = subst-var S p p∈τ
... | no _ = var p (sets-lemma {σ} {τ} p (τ⊆σ S) p∈σ∪τ)
(¬′ ϕ) [ S ] = ¬′ (ϕ [ S ])
(ϕ₁ ∧′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ∧′ (ϕ₂ [ S ])
(ϕ₁ ∨′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ∨′ (ϕ₂ [ S ])
(ϕ₁ →′ ϕ₂) [ S ] = (ϕ₁ [ S ]) →′ (ϕ₂ [ S ])
(ϕ₁ ↔′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ↔′ (ϕ₂ [ S ])

module example-3-7-2 where
  σ : Signature
  σ = λ k → k < 4

  τ : Signature
  τ = λ k → k > 0 × k < 4

  σ-dec : Decidable σ
  σ-dec p = p <? 4

  τ-dec : Decidable τ
  τ-dec p with p >? 0 | p <? 4
  ... | yes prf₁ | yes prf₂ = yes (prf₁ , prf₂)
  ... | no prf₁  | yes prf₂ = no (λ z → prf₁ (proj₁ z))
  ... | yes prf₁ | no prf₂ = no (λ z → prf₂ (proj₂ z))
  ... | no prf₁  | no prf₂ = no (λ z → prf₂ (proj₂ z))

  p₀ p₁ p₂ p₃ : LP (σ ∪ τ)
  p₀ = var 0 (inj₁ (s≤s z≤n))
  p₁ = var 1 (inj₁ (s≤s (s≤s z≤n)))
  p₂ = var 2 (inj₁ (s≤s (s≤s (s≤s z≤n))))
  p₃ = var 3 (inj₁ (s≤s (s≤s (s≤s (s≤s z≤n)))))

  p₀′ p₁′ p₂′ p₃′ : LP σ
  p₀′ = var 0 (s≤s z≤n)
  p₁′ = var 1 (s≤s (s≤s z≤n))
  p₂′ = var 2 (s≤s (s≤s (s≤s z≤n)))
  p₃′ = var 3 (s≤s (s≤s (s≤s (s≤s z≤n))))

  ϕ : LP (σ ∪ τ)
  ϕ = (p₁ →′ (p₂ ∧′ (¬′ p₃))) ↔′ p₃

  ψ₁ ψ₂ ψ₃ : LP σ
  ψ₁ = ¬′ (¬′ p₃′)
  ψ₂ = p₀′
  ψ₃ = p₁′ →′ p₂′

  f : (p : ℕ) → p ∈ τ → LP σ
  f 0 ()
  f (suc 0) _ = ψ₁
  f (suc (suc 0)) _ = ψ₂
  f (suc (suc (suc 0))) _ = ψ₃
  f (suc (suc (suc (suc _)))) (_ , s≤s (s≤s (s≤s (s≤s ()))))

  S : Substitution σ τ
  S = substitution τ-dec proj₂ f

  ϕ′ : LP σ
  ϕ′ = ϕ [ S ]

  _ : ϕ′ ≡ (((¬′ (¬′ p₃′)) →′ (p₀′ ∧′ (¬′ (p₁′ →′ p₂′)))) ↔′
              (p₁′ →′ p₂′))
  _ = refl

{-
Definition 3.7.4
-}
_[_]ₛ : ∀ {σ τ} → Structure σ → Substitution σ τ → Structure (σ ∪ τ)
(A′ [ S ]ₛ) p p∈σ∪τ with dec S p
... | yes p∈τ =  A′ * (subst-var S p p∈τ)
... | no _ with p∈σ∪τ
...        | inj₁ p∈σ = A′ p p∈σ
...        | inj₂ p∈τ = A′ p (τ⊆σ S p∈τ)

{-
Lemma 3.7.5
-}
lemma-3-7-5
  : ∀ {σ τ}
  → (A′ : Structure σ) (ϕ : LP (σ ∪ τ)) (S : Substitution σ τ)
  → A′ * (ϕ [ S ]) ≡ (A′ [ S ]ₛ) * ϕ
lemma-3-7-5 A′ ⊥′ S = refl
lemma-3-7-5 A′ (var p p∈σ∪τ) S with dec S p | p∈σ∪τ
lemma-3-7-5 A′ (var p p∈σ∪τ) S | yes p∈τ | _        = refl
lemma-3-7-5 A′ (var p p∈σ∪τ) S | no ¬p∈τ | inj₁ p∈σ = refl
lemma-3-7-5 A′ (var p p∈σ∪τ) S | no ¬p∈τ | inj₂ p∈τ = refl
lemma-3-7-5 A′ (¬′ ϕ) S = cong not (lemma-3-7-5 A′ ϕ S)
lemma-3-7-5 A′ (ϕ₁ ∧′ ϕ₂) S =
  cong₂ _∧_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ ∨′ ϕ₂) S =
  cong₂ _∨_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ →′ ϕ₂) S =
  cong₂ _⇒b_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ ↔′ ϕ₂) S =
  cong₂ _⇔b_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)

{-
Theorem 3.7.6.a
-}
theorem-3-7-6-a
  : ∀ {σ τ}
  → (ϕ₁ ϕ₂ : LP (σ ∪ τ))
  → (S : Substitution σ τ)
  → ϕ₁ ~ ϕ₂
  → (ϕ₁ [ S ]) ~ (ϕ₂ [ S ])
theorem-3-7-6-a ϕ₁ ϕ₂ S ϕ₁~ϕ₂ A′ = begin
  (A′ * (ϕ₁ [ S ]))
    ≡⟨ lemma-3-7-5 A′ ϕ₁ S ⟩
  (A′ [ S ]ₛ) * ϕ₁
    ≡⟨ ϕ₁~ϕ₂ (A′ [ S ]ₛ) ⟩
  (A′ [ S ]ₛ) * ϕ₂
    ≡⟨ sym (lemma-3-7-5 A′ ϕ₂ S) ⟩
  (A′ * (ϕ₂ [ S ]))
    ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

_~ₛ_ : ∀ {σ τ} (S₁ S₂ : Substitution σ τ) → Set₁
S₁ ~ₛ S₂ = ∀ (ϕ : LP _) → (ϕ [ S₁ ]) ~ (ϕ [ S₂ ])

_≅ₛ_ : ∀ {σ} (A₁ A₂ : Structure σ) → Set
_≅ₛ_ {σ} A₁ A₂ = ∀ (p : ℕ) (prf : p ∈ σ) → A₁ p prf ≡ A₂ p prf

structure-cong
  : ∀ {σ} {A′ B′ : Structure σ}
  → (ϕ : LP σ)
  → A′ ≅ₛ B′
  → A′ * ϕ ≡ B′ * ϕ
structure-cong ⊥′ prf = refl
structure-cong (var p p∈σ) prf = prf p p∈σ
structure-cong (¬′ ϕ) prf = cong not (structure-cong ϕ prf)
structure-cong (ϕ₁ ∧′ ϕ₂) prf =
  cong₂ _∧_ (structure-cong ϕ₁ prf) (structure-cong ϕ₂ prf)
structure-cong (ϕ₁ ∨′ ϕ₂) prf =
  cong₂ _∨_ (structure-cong ϕ₁ prf) (structure-cong ϕ₂ prf)
structure-cong (ϕ₁ →′ ϕ₂) prf =
  cong₂ _⇒b_ (structure-cong ϕ₁ prf) (structure-cong ϕ₂ prf)
structure-cong (ϕ₁ ↔′ ϕ₂) prf =
  cong₂ _⇔b_ (structure-cong ϕ₁ prf) (structure-cong ϕ₂ prf)

theorem-3-7-6-b-lemma
  : ∀ {σ τ}
  → (A′ : Structure σ)
  → (S₁ S₂ : Substitution σ τ)
  → S₁ ~ₛ S₂
  → (A′ [ S₁ ]ₛ) ≅ₛ (A′ [ S₂ ]ₛ)
theorem-3-7-6-b-lemma A′ S₁ S₂ S₁~S₂ p prf
  with dec S₁ p | dec S₂ p | prf    | S₁~S₂ (var p prf) A′
... | yes _     | yes _    | _      | [S₁~S₂]              = [S₁~S₂]
... | yes _     | no _     | inj₁ _ | [S₁~S₂]              = [S₁~S₂]
... | yes _     | no _     | inj₂ _ | [S₁~S₂]              = [S₁~S₂]
... | no _      | yes _    | inj₁ _ | [S₁~S₂]              = [S₁~S₂]
... | no _      | yes _    | inj₂ _ | [S₁~S₂]              = [S₁~S₂]
... | no _      | no _     | inj₁ _ | [S₁~S₂]              = [S₁~S₂]
... | no _      | no _     | inj₂ _ | [S₁~S₂]              = [S₁~S₂]

theorem-3-7-6-b
  : ∀ {σ τ}
  → (ϕ : LP (σ ∪ τ))
  → (S₁ S₂ : Substitution σ τ)
  → S₁ ~ₛ S₂
  → (ϕ [ S₁ ]) ~ (ϕ [ S₂ ])
theorem-3-7-6-b ϕ S₁ S₂ S₁~S₂ A′ =
  (A′ * (ϕ [ S₁ ]))
    ≡⟨ lemma-3-7-5 A′ ϕ S₁ ⟩
  (A′ [ S₁ ]ₛ) * ϕ
    ≡⟨ structure-cong ϕ (theorem-3-7-6-b-lemma A′ S₁ S₂ S₁~S₂) ⟩
  (A′ [ S₂ ]ₛ) * ϕ
    ≡⟨ sym (lemma-3-7-5 A′ ϕ S₂) ⟩
  (A′ * (ϕ [ S₂ ]))
    ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

unit-structure : Bool → FiniteStructure 1
unit-structure b ℕ.zero (s≤s z≤n) = b
unit-structure b (suc ℕ.zero) (s≤s ())

1-structure-is-true-or-false : (A′ : FiniteStructure 1) → A′ ≡ unit-structure false ⊎ A′ ≡ unit-structure true
1-structure-is-true-or-false A′ with A′ ℕ.zero (s≤s z≤n) ≟ false
1-structure-is-true-or-false A′ | yes prf = inj₁ (funExt λ p → funExt (λ x → helper p x))
  where
    helper
      : (p : ℕ)
      → (x : suc p Data.Nat.≤ 1)
      → A′ p x ≡ unit-structure false p x
    helper ℕ.zero (s≤s z≤n) = prf
    helper (suc p) (s≤s ())
1-structure-is-true-or-false A′ | no prf′ with ¬f→t prf′
1-structure-is-true-or-false A′ | no prf′ | prf = inj₂ (funExt λ p → funExt (λ x → helper p x))
  where
    helper
      : (p : ℕ)
      → (x : suc p Data.Nat.≤ 1)
      → A′ p x ≡ unit-structure true p x
    helper ℕ.zero (s≤s z≤n) = prf
    helper (suc p) (s≤s ())

weaken-struct
  : ∀ n
  → (Structure (FiniteSignature (suc n)))
  → (Structure (FiniteSignature n))
weaken-struct n A′ p prf = A′ p (≤-step prf)

strengthen-struct
  : ∀ n
  → Bool
  → FiniteStructure n
  → FiniteStructure (suc n)
strengthen-struct n b A′ p _ with p <? n
... | yes prf = A′ p prf
... | no _ = b

weaken-struct-fun
  : ∀ n
  → (FiniteStructure (suc n) → Bool)
  → Bool
  → (FiniteStructure n → Bool)
weaken-struct-fun n f b A′ = f (strengthen-struct n b A′)

{-
{-
Theorem 3.8.4
-}
posts-theorem
  : (n : ℕ)
  → let σ = FiniteSignature n in
    (Satisfiable σ)
  → (g : Structure σ → Bool)
  → Σ[ ψ ∈ LP σ ] g ≡ _* ψ
posts-theorem (suc ℕ.zero) _ g
    with g (unit-structure false) ≟ true | g (unit-structure true) ≟ true
posts-theorem (suc ℕ.zero) sat g | yes prf₁ | no prf₂ =
  (¬′ var ℕ.zero (s≤s z≤n)) ,
  funExt helper
  where
    helper : (A′ : Structure _) → g A′ ≡ not (A′ 0 (s≤s z≤n))
    helper A′ with 1-structure-is-true-or-false A′
    ... | inj₁ refl = prf₁
    ... | inj₂ refl = ¬t→f prf₂
posts-theorem (suc ℕ.zero) _ g | no prf₁ | yes prf₂ =
  (var ℕ.zero (s≤s z≤n)) ,
  funExt helper
    where
    helper : (A′ : Structure _) → g A′ ≡ A′ 0 (s≤s z≤n)
    helper A′ with 1-structure-is-true-or-false A′
    ... | inj₁ refl = ¬t→f prf₁
    ... | inj₂ refl = prf₂
posts-theorem (suc ℕ.zero) _ g | no _ | no _ = {!!}
posts-theorem (suc ℕ.zero) _ g | yes _ | yes _ = {!!}
posts-theorem (suc (suc n)) _ g
    with g (unit-structure false) ≟ true | g (unit-structure true) ≟ true
posts-theorem (suc (suc n)) _ g | yes prf₁ | no prf₂ =
  let
    ind-f =
      posts-theorem
        (suc n)
        (ℕ.zero , s≤s z≤n)
        (weaken-struct-fun (suc n) g false)
    ind-t =
      posts-theorem
        (suc n)
        (ℕ.zero , s≤s z≤n)
        (weaken-struct-fun (suc n) g true)
  in {!!}
posts-theorem (suc (suc n)) _ g | no prf₁ | yes prf₂ = ?
posts-theorem (suc (suc n)) _ g | no prf₁ | no prf₂ = ?
posts-theorem (suc (suc n)) _ g | yes prf₁ | yes prf₂ = ?
-- -}

open Relation.Binary.PropositionalEquality.≡-Reasoning

data Table : ℕ → Set where
  constant : Bool → Table 0
  branch : ∀ {n} → Table n → Table n → Table (suc n)

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

fun→table
  : ∀ n
  → (Structure (FiniteSignature (suc n)) → Bool)
  → Table (suc n)
fun→table 0 g =
  branch
    (constant (g (unit-structure true)))
    (constant (g (unit-structure false)))
fun→table (suc n) g =
  branch
    (fun→table n (weaken-struct-fun (suc n) g true))
    (fun→table n (weaken-struct-fun (suc n) g false))

table→fun
  : ∀ n
  → Table (suc n)
  → (Structure (FiniteSignature (suc n)) → Bool)
table→fun 0 (branch (constant a) (constant b)) A′ with A′ 0 (s≤s z≤n)
... | true = a
... | false = b
table→fun (suc n) (branch t₁ t₂) A′ with A′ (suc n) (s≤s (s≤s ≤-refl))
... | true = table→fun n t₁ (weaken-struct (suc n) A′)
... | false = table→fun n t₂ (weaken-struct (suc n) A′)

{-
table→fun-zero
  : ∀ A′ (f : FiniteStructure 1 → Bool)
  → table→fun 0
      (branch
        (constant (f (unit-structure true)))
        (constant (f (unit-structure false)))
      )
      A′
  ≡ f A′
table→fun-zero A′ f with A′ 0 (s≤s z≤n) ≟ unit-structure true 0 (s≤s z≤n)
table→fun-zero A′ f | yes prf with A′ 0 (s≤s z≤n)
table→fun-zero A′ f | yes prf | true = {!!}
table→fun-zero A′ f | yes prf | false = {!!}
table→fun-zero A′ f | no prf = {!!}
-}

strengthen-struct-reduce
  : ∀ n b A′ p prf
  → strengthen-struct n b A′ p (≤-step prf) ≡ A′ p prf
strengthen-struct-reduce n b A′ p prf with p <? n
... | yes prf′ = cong (A′ p) (<-irrelevant prf′ prf)
... | no ¬prf = ⊥-elim (¬prf prf)

weaken-strengthen
  : ∀ n b A′
  → weaken-struct n (strengthen-struct n b A′) ≡ A′
weaken-strengthen n b A′ = funExt λ p → funExt λ prf →
  begin
    weaken-struct n (strengthen-struct n b A′) p prf
  ≡⟨⟩
    strengthen-struct n b A′ p (≤-step prf)
  ≡⟨ strengthen-struct-reduce n b A′ p prf ⟩
    A′ p prf
  ∎

strengthen-struct-true
  : ∀ n b A′
  → strengthen-struct (suc n) b A′ (suc n) (s≤s (s≤s ≤-refl)) ≡ b
strengthen-struct-true n b A′ with suc n <? suc n
... | yes s-n<s-n = ⊥-elim (<-irrefl refl s-n<s-n)
... | no _ = refl

table→fun-strengthen
  : ∀ n b t₁ t₂ A′
  → table→fun (suc n) (branch t₁ t₂) (strengthen-struct (suc n) b A′)
  ≡ table→fun n (if b then t₁ else t₂) A′
table→fun-strengthen n true t₁ t₂ A′ rewrite strengthen-struct-true n true A′ =
  begin
    table→fun n t₁ (weaken-struct (suc n) (strengthen-struct (suc n) true A′))
  ≡⟨ cong (table→fun n t₁) (weaken-strengthen (suc n) true A′) ⟩
    table→fun n t₁ A′
  ∎
table→fun-strengthen n false t₁ t₂ A′ rewrite strengthen-struct-true n false A′ =
  begin
    table→fun n t₂ (weaken-struct (suc n) (strengthen-struct (suc n) false A′))
  ≡⟨ cong (table→fun n t₂) (weaken-strengthen (suc n) false A′) ⟩
    table→fun n t₂ A′
  ∎

table→fun-strengthen′
  : ∀ n b t₁ t₂
  → (λ A′ → table→fun (suc n) (branch t₁ t₂) (strengthen-struct (suc n) b A′))
  ≡ (λ A′ → table→fun n (if b then t₁ else t₂) A′)
table→fun-strengthen′ n b t₁ t₂ = funExt (table→fun-strengthen n b t₁ t₂)

table→fun→table
  : ∀ n t
  → fun→table n (table→fun n t) ≡ t
table→fun→table ℕ.zero (branch (constant a) (constant b)) = refl
table→fun→table (suc n) (branch t₁ t₂) =
  begin
    fun→table (suc n) (table→fun (suc n) (branch t₁ t₂))
  ≡⟨⟩
    branch
      (fun→table n (weaken-struct-fun (suc n) (table→fun (suc n) (branch t₁ t₂)) true))
      (fun→table n (weaken-struct-fun (suc n) (table→fun (suc n) (branch t₁ t₂)) false))
  ≡⟨⟩
    branch
      (fun→table
        n
        (λ A′ →
          table→fun
            (suc n)
            (branch t₁ t₂)
            (strengthen-struct (suc n) true A′)
          )
      )
      (fun→table
        n
          (λ A′ →
            table→fun
              (suc n)
              (branch t₁ t₂)
              (strengthen-struct (suc n) false A′)
          )
      )
  ≡⟨
    cong₂
      (λ a b → branch (fun→table n a) (fun→table n b))
      (table→fun-strengthen′ n true t₁ t₂)
      (table→fun-strengthen′ n false t₁ t₂)
  ⟩
    branch
      (fun→table n (table→fun n t₁))
      (fun→table n (table→fun n t₂))
  ≡⟨ cong₂ branch (table→fun→table n t₁) (table→fun→table n t₂) ⟩
    branch t₁ t₂
  ∎

{-
fun→table→fun
  : ∀ n f
  → table→fun n (fun→table n f) ≡ f
fun→table→fun 0 f =
  begin
    table→fun 0 (fun→table 0 f)
  ≡⟨⟩
    table→fun 0
      (branch
        (constant (f (unit-structure true)))
        (constant (f (unit-structure false)))
      )
  ≡⟨ {!!} ⟩
    f
  ∎
fun→table→fun (suc n) f = {!!}
-}

table→fun′
  : ∀ {n}
  → Table n
  → (FiniteStructure n → Bool)
table→fun′ {0} (constant b) A′ = b
table→fun′ {suc n} (branch t₁ t₂) A′ with A′ n (s≤s ≤-refl)
... | true = table→fun′ t₁ (weaken-struct _ A′)
... | false = table→fun′ t₂ (weaken-struct _ A′)

fun→table′
  : ∀ {n}
  → (Structure (FiniteSignature n) → Bool)
  → Table n
fun→table′ {0} g = constant (g empty-structure)
fun→table′ {suc _} g =
  branch
    (fun→table′ (weaken-struct-fun _ g true))
    (fun→table′ (weaken-struct-fun _ g false))

get-table : ∀ {n} → LP (FiniteSignature n) → Table n
get-table {0} ψ = constant (empty-structure * ψ)
get-table {suc _} ψ = fun→table′ (_* ψ)

_ : ∀ {n} → Table n ≡ (Vec Bool n → Bool)
_ = {!!}

_ : ∀ {n} → FiniteStructure n ≡ Vec Bool n
_ = {!!}

_ : ∀ {n} → (FiniteStructure n → Bool) ≡ (Vec Bool n → Bool)
_ = {!!}

_ : ∀ {n} → (FiniteStructure n → Bool) ≡ Table n
_ = {!!}

weaken-prop : ∀ {n} → LP (FiniteSignature n) → LP (FiniteSignature (suc n))
weaken-prop ⊥′ = ⊥′
weaken-prop (var p prf) = var p (≤-step prf)
weaken-prop (¬′ ψ) = ¬′ weaken-prop ψ
weaken-prop (ψ₁ ∧′ ψ₂) = weaken-prop ψ₁ ∧′ weaken-prop ψ₂
weaken-prop (ψ₁ ∨′ ψ₂) = weaken-prop ψ₁ ∨′ weaken-prop ψ₂
weaken-prop (ψ₁ →′ ψ₂) = weaken-prop ψ₁ →′ weaken-prop ψ₂
weaken-prop (ψ₁ ↔′ ψ₂) = weaken-prop ψ₁ ↔′ weaken-prop ψ₂

strengthen-struct-weaken-prop
  : ∀ {n b A′} ψ
  → strengthen-struct n b A′ * weaken-prop ψ
  ≡ A′ * ψ
strengthen-struct-weaken-prop ⊥′ = refl
strengthen-struct-weaken-prop {n} {_} {A′} (var p prf) with p <? n
... | yes prf′ = cong (A′ p) (<-irrelevant prf′ prf)
... | no ¬prf = ⊥-elim (¬prf prf)
strengthen-struct-weaken-prop (¬′ ψ) =
  cong not (strengthen-struct-weaken-prop ψ)
strengthen-struct-weaken-prop (ψ₁ ∧′ ψ₂) =
  cong₂
    _∧_
    (strengthen-struct-weaken-prop ψ₁)
    (strengthen-struct-weaken-prop ψ₂)
strengthen-struct-weaken-prop (ψ₁ ∨′ ψ₂) =
  cong₂
    _∨_
    (strengthen-struct-weaken-prop ψ₁)
    (strengthen-struct-weaken-prop ψ₂)
strengthen-struct-weaken-prop (ψ₁ →′ ψ₂) =
  cong₂
    _⇒b_
    (strengthen-struct-weaken-prop ψ₁)
    (strengthen-struct-weaken-prop ψ₂)
strengthen-struct-weaken-prop (ψ₁ ↔′ ψ₂) =
  cong₂
    _⇔b_
    (strengthen-struct-weaken-prop ψ₁)
    (strengthen-struct-weaken-prop ψ₂)

weaken-fun-disj
  : ∀ n ψ₁ ψ₂ A′ b
  → weaken-struct-fun
      n
      (_*
        ((var n ≤-refl ∧′ weaken-prop ψ₁)
        ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
      )
      b
      A′
  ≡ A′ * (if b then ψ₁ else ψ₂)
weaken-fun-disj n ψ₁ ψ₂ A′ b with n <? n
... | yes prf = ⊥-elim (<-irrefl refl prf)
... | no _ with b
... | true =
  begin
    (strengthen-struct n true A′ * weaken-prop ψ₁) ∨ false
  ≡⟨ ∨-identityʳ _ ⟩
    strengthen-struct n true A′ * weaken-prop ψ₁
  ≡⟨ strengthen-struct-weaken-prop ψ₁ ⟩
    A′ * ψ₁
  ∎
... | false = strengthen-struct-weaken-prop ψ₂

posts-theorem-on-tables
  : ∀ {n}
  → (t : Table n)
  → Σ[ ψ ∈ LP (FiniteSignature n) ] get-table ψ ≡ t
posts-theorem-on-tables (constant true) = (⊥′ →′ ⊥′) , refl
posts-theorem-on-tables (constant false) = ⊥′ , refl
posts-theorem-on-tables {1} (branch (constant false) (constant false)) =
  ⊥′ , refl
posts-theorem-on-tables {1} (branch (constant false) (constant true)) =
  ¬′ var 0 (s≤s z≤n) , refl
posts-theorem-on-tables {1} (branch (constant true) (constant false)) =
  var 0 (s≤s z≤n) , refl
posts-theorem-on-tables {1} (branch (constant true) (constant true)) =
  ⊥′ →′ ⊥′ , refl
posts-theorem-on-tables {suc n@(suc _)} (branch t₁ t₂)
    with posts-theorem-on-tables t₁ | posts-theorem-on-tables t₂
... | ψ₁ , prf₁ | ψ₂ , prf₂ =
  (
    (var n ≤-refl ∧′ weaken-prop ψ₁)
    ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂)
  )
  , (
    begin
      fun→table′
        (_*
          ((var n ≤-refl ∧′ weaken-prop ψ₁)
          ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
        )
    ≡⟨⟩
      branch
        (fun→table′
          (weaken-struct-fun
            _
            (_*
              ((var n ≤-refl ∧′ weaken-prop ψ₁)
              ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
            )
            true
          )
        )
        (fun→table′
          (weaken-struct-fun
            _
            (_*
              ((var n ≤-refl ∧′ weaken-prop ψ₁)
              ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
            )
            false
          )
        )
    ≡⟨
        cong₂
          (λ a b → branch (fun→table′ a) (fun→table′ b))
          (funExt λ A′ → weaken-fun-disj n ψ₁ ψ₂ A′ true)
          (funExt λ A′ → weaken-fun-disj n ψ₁ ψ₂ A′ false)
    ⟩
      branch
        (fun→table′ (_* ψ₁))
        (fun→table′ (_* ψ₂))
    ≡⟨ cong₂ branch prf₁ prf₂ ⟩
      branch t₁ t₂
    ∎
  )

constant-inj
  : ∀ {a b}
  → constant a ≡ constant b
  → a ≡ b
constant-inj refl = refl

isContr-finiteStructure0 : ∀ (p : FiniteStructure 0) → p ≡ empty-structure
isContr-finiteStructure0 p =
  funExt (λ x → funExt (λ prf → helper p x prf))
  where
    helper : ∀ (p : FiniteStructure 0) x prf → p x prf ≡ empty-structure x prf
    helper p n ()

get-table-fun→table
  : ∀ n (ψ : LP (FiniteSignature n)) g
  → get-table ψ ≡ fun→table′ g
  → (_* ψ) ≡ g
get-table-fun→table ℕ.zero ψ g prf =
  funExt helper₂
  where
    helper₁ : (empty-structure * ψ) ≡ g empty-structure
    helper₁ = constant-inj prf

    helper₂ : ∀ p → (p * ψ) ≡ g p
    helper₂ p rewrite isContr-finiteStructure0 p = helper₁
get-table-fun→table (suc n) ψ g prf =
  funExt {!!}
  where
    ind₁ = get-table-fun→table n {!ψ!} {!!} {!!}

{-
Theorem 3.8.4
-}
posts-theorem
  : (n : ℕ)
  → let σ = FiniteSignature n
  in (g : Structure σ → Bool)
  → Σ[ ψ ∈ LP σ ]  _* ψ ≡ g
posts-theorem n g with posts-theorem-on-tables (fun→table′ g)
... | ψ , prf = ψ , get-table-fun→table n ψ g prf
