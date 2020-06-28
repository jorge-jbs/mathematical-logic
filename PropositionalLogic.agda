{-
Formalization of Propositional Logic following "Mathematical Logic" of
Ian Chiswell and Wilfrid Hodges.
-}

{-# OPTIONS --without-K --safe #-}
--{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level using (Level; 0ℓ; _⊔_)
open import Axiom.Extensionality.Propositional using (Extensionality)

module PropositionalLogic (funExt : Extensionality 0ℓ 0ℓ) where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool
  using (Bool; false; true; _≟_; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec using (Vec)
import Data.Vec as V
open import Data.List using (List)
import Data.List as L
open import Data.List.Relation.Unary.All using (All)
import Data.List.Membership.Propositional as L
import Data.List.Relation.Unary.Any as L using (here; there)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Nat using (ℕ; suc; _<_; _<?_; _>_; _>?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step; <-irrefl; <-irrelevant)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,′_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Equivalence using (_⇔_; Equivalence; equivalence)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary
  using (Pred; Decidable; Satisfiable; ∅; _∪_; _⊆_)
  renaming (｛_｝ to ⟦_⟧)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.PropositionalEquality.Core using (subst)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)

open import Utils

max : ℕ → ℕ → ℕ
max 0 m = m
max (suc n) 0 = suc n
max (suc n) (suc m) = max n m

Signature : Set₁
Signature = Pred ℕ 0ℓ

finite-signature : ℕ → Signature
finite-signature n = λ k → k < n

_∈_ : {a ℓ : Level} {A : Set a} (a : A) → Pred A ℓ → Set ℓ
p ∈ σ = σ p

private
  variable
    σ τ : Signature

data LP : (σ : Signature) → Set₁ where
  ⊥′ : LP σ
  var : (p : ℕ) → p ∈ σ → LP σ
  ¬′_ : LP σ → LP σ
  _∧′_ _∨′_ _→′_ _↔′_ : LP σ → LP σ → LP σ

private
  variable
    ψ ϕ χ : LP σ

height : LP σ → ℕ
height ⊥′ = 0
height (var p _) = 0
height (¬′ ψ) = suc (height ψ)
height (ϕ ∧′ ψ) = max (height ϕ) (height ψ)
height (ϕ ∨′ ψ) = max (height ϕ) (height ψ)
height (ϕ →′ ψ) = max (height ϕ) (height ψ)
height (ϕ ↔′ ψ) = max (height ϕ) (height ψ)

Assumptions : (σ : Signature) → Set₂
Assumptions σ = Pred (LP σ) (Level.suc 0ℓ)

private
  variable
    Γ Δ : Assumptions σ

infixr 3 _⊢_

{-
Definition 3.4.1 (σ-derivation) and 3.4.4 (σ-sequent). Merged thanks to
dependent types.
-}
data _⊢_
    : (Γ : Assumptions σ)
    → (conclusion : LP σ)
    → Set₂ where
  weakening
    : Γ ⊆ Δ
    → Γ ⊢ ϕ
    → Δ ⊢ ϕ
  axiom
    : (ϕ : LP σ)
    → ⟦ ϕ ⟧ ⊢ ϕ
  -- Can this be proven? (without making it an axiom)
  transitive
    : Δ ⊢ ψ
    → (∀ δ → δ ∈ Δ → Γ ⊢ δ)
    → Γ ⊢ ψ
  →-intro
    : (ϕ ψ : LP σ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ ψ
    → Γ ⊢ (ϕ →′ ψ)
  ¬-intro
    : (ϕ : LP σ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ ⊥′
    → Γ ⊢ (¬′ ϕ)
  RAA
    : (ϕ : LP σ)
    → (Γ ∪ ⟦ ¬′ ϕ ⟧) ⊢ ⊥′
    → Γ ⊢ ϕ
  →-elim
    : Γ ⊢ ϕ
    → Γ ⊢ (ϕ →′ ψ)
    → Γ ⊢ ψ
  ∨-elim
    : Γ           ⊢ (ϕ ∨′ ψ)
    → (Γ ∪ ⟦ ϕ ⟧) ⊢ χ
    → (Γ ∪ ⟦ ψ ⟧) ⊢ χ
    → Γ ⊢ χ
  -- TODO: add the rest of the derivation rules

{-
Definition 3.5.3 (σ-structure).
-}
Structure : (σ : Signature) → Set
Structure σ = (p : ℕ) → (p ∈ σ) → Bool

private
  variable
    A B : Structure σ

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

{-
Definition 3.5.7 (tautology)
-}
⊨ : ∀ {σ} (ϕ : LP σ) → Set
⊨ {σ} ϕ = ∀ {A′ : Structure σ} → A′ * ϕ ≡ true

{-
Lemma 3.6.1
-}
module lemma-3-6-1 (ϕ ψ : LP σ) where
  I : Set
  I = ∀ A → A * ϕ ≡ true ⇔ A * ψ ≡ true

  II : Set
  II = ∀ A → A * ϕ ≡ A * ψ

  III : Set
  III = ⊨ (ϕ ↔′ ψ)

  Lemma : Set
  Lemma = I ⇔ II × II ⇔ III

  i→ii : I → II

  i→ii i-prf A with A * ϕ ≟ true | A * ψ ≟ true
  i→ii i-prf A | yes ϕ-true | yes ψ-true
      rewrite ϕ-true | ψ-true =
    refl

  i→ii i-prf A | no ϕ-false | no ψ-false
      rewrite ¬t→f ϕ-false | ¬t→f ψ-false =
    refl

  i→ii i-prf A | no _       | yes ψ-true
      rewrite ψ-true with Equivalence.from (i-prf A) ⟨$⟩ ψ-true
  i→ii i-prf A | no _       | yes ψ-true | prf =
    prf

  i→ii i-prf A | yes ϕ-true | no _
      rewrite ϕ-true with Equivalence.to (i-prf A) ⟨$⟩ ϕ-true
  i→ii i-prf A | yes ϕ-true | no _       | prf =
    sym prf

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
_~_ : Rel (LP σ) 0ℓ
ϕ ~ ψ = II
  where open lemma-3-6-1 ϕ ψ

{-
Theorem 3.6.4
-}
~-is-equivalence : IsEquivalence (_~_ {σ})
~-is-equivalence =
  record
    { refl = λ A → refl
    ; sym = λ x~y A → sym (x~y A)
    ; trans = λ x~y y~z A → trans (x~y A) (y~z A)
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

sets-lemma : (p : ℕ) → τ ⊆ σ → p ∈ (σ ∪ τ) → p ∈ σ
sets-lemma p τ⊆σ p∈σ∪τ with p∈σ∪τ
... | inj₁ p∈σ = p∈σ
... | inj₂ p∈τ = τ⊆σ p∈τ

weaken-term-signature : LP σ → LP (σ ∪ τ)
weaken-term-signature ⊥′ = ⊥′
weaken-term-signature (var p p∈σ) = var p (inj₁ p∈σ)
weaken-term-signature (¬′ ϕ) = ¬′ weaken-term-signature ϕ
weaken-term-signature (ϕ₁ ∧′ ϕ₂) = weaken-term-signature ϕ₁ ∧′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ ∨′ ϕ₂) = weaken-term-signature ϕ₁ ∨′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ →′ ϕ₂) = weaken-term-signature ϕ₁ →′ weaken-term-signature ϕ₂
weaken-term-signature (ϕ₁ ↔′ ϕ₂) = weaken-term-signature ϕ₁ ↔′ weaken-term-signature ϕ₂

_[_] : LP (σ ∪ τ) → Substitution σ τ → LP σ
⊥′ [ S ] = ⊥′
_[_] {σ} {τ} (var p p∈σ∪τ) S with dec S p
... | yes p∈τ = subst-var S p p∈τ
... | no _ = var p (sets-lemma {τ} {σ} p (τ⊆σ S) p∈σ∪τ)
(¬′ ϕ) [ S ] = ¬′ (ϕ [ S ])
(ϕ₁ ∧′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ∧′ (ϕ₂ [ S ])
(ϕ₁ ∨′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ∨′ (ϕ₂ [ S ])
(ϕ₁ →′ ϕ₂) [ S ] = (ϕ₁ [ S ]) →′ (ϕ₂ [ S ])
(ϕ₁ ↔′ ϕ₂) [ S ] = (ϕ₁ [ S ]) ↔′ (ϕ₂ [ S ])

{-
Definition 3.7.4
-}
_[_]ₛ : Structure σ → Substitution σ τ → Structure (σ ∪ τ)
(A′ [ S ]ₛ) p p∈σ∪τ with dec S p
... | yes p∈τ =  A′ * (subst-var S p p∈τ)
... | no _ with p∈σ∪τ
...        | inj₁ p∈σ = A′ p p∈σ
...        | inj₂ p∈τ = A′ p (τ⊆σ S p∈τ)

{-
Lemma 3.7.5

-}
lemma-3-7-5
  : {S : Substitution σ τ} (ϕ : LP (σ ∪ τ))
  → A * (ϕ [ S ]) ≡ (A [ S ]ₛ) * ϕ
lemma-3-7-5 ⊥′ = refl
lemma-3-7-5 {S = S} (var p p∈σ∪τ) with dec S p | p∈σ∪τ
lemma-3-7-5 (var p p∈σ∪τ) | yes p∈τ | _        = refl
lemma-3-7-5 (var p p∈σ∪τ) | no ¬p∈τ | inj₁ p∈σ = refl
lemma-3-7-5 (var p p∈σ∪τ) | no ¬p∈τ | inj₂ p∈τ = refl
lemma-3-7-5 (¬′ ϕ) = cong not (lemma-3-7-5 ϕ)
lemma-3-7-5 (ϕ₁ ∧′ ϕ₂) =
  cong₂ _∧_ (lemma-3-7-5 ϕ₁) (lemma-3-7-5 ϕ₂)
lemma-3-7-5 (ϕ₁ ∨′ ϕ₂) =
  cong₂ _∨_ (lemma-3-7-5 ϕ₁) (lemma-3-7-5 ϕ₂)
lemma-3-7-5 (ϕ₁ →′ ϕ₂) =
  cong₂ _⇒b_ (lemma-3-7-5 ϕ₁) (lemma-3-7-5 ϕ₂)
lemma-3-7-5 (ϕ₁ ↔′ ϕ₂) =
  cong₂ _⇔b_ (lemma-3-7-5 ϕ₁) (lemma-3-7-5 ϕ₂)

{-
Theorem 3.7.6.a
-}
theorem-3-7-6-a
  : (ϕ₁ ϕ₂ : LP (σ ∪ τ))
  → (S : Substitution σ τ)
  → ϕ₁ ~ ϕ₂
  → (ϕ₁ [ S ]) ~ (ϕ₂ [ S ])
theorem-3-7-6-a ϕ₁ ϕ₂ S ϕ₁~ϕ₂ A′ = begin
  (A′ * (ϕ₁ [ S ]))
    ≡⟨ lemma-3-7-5 ϕ₁ ⟩
  (A′ [ S ]ₛ) * ϕ₁
    ≡⟨ ϕ₁~ϕ₂ (A′ [ S ]ₛ) ⟩
  (A′ [ S ]ₛ) * ϕ₂
    ≡⟨ sym (lemma-3-7-5 ϕ₂) ⟩
  (A′ * (ϕ₂ [ S ]))
    ∎

_~ₛ_ : (S₁ S₂ : Substitution σ τ) → Set₁
S₁ ~ₛ S₂ = ∀ (ϕ : LP _) → (ϕ [ S₁ ]) ~ (ϕ [ S₂ ])

theorem-3-7-6-b-lemma
  : (S₁ S₂ : Substitution σ τ)
  → S₁ ~ₛ S₂
  → (A [ S₁ ]ₛ) ≡ (A [ S₂ ]ₛ)
theorem-3-7-6-b-lemma S₁ S₂ S₁~S₂ =
  funExt λ p → funExt λ prf → lemma p prf
  where
    lemma : ∀ p prf → (A [ S₁ ]ₛ) p prf ≡ (A [ S₂ ]ₛ) p prf
    lemma p prf
        with dec S₁ p | dec S₂ p | prf    | S₁~S₂ (var p prf) _
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
    ≡⟨ lemma-3-7-5 ϕ ⟩
  (A′ [ S₁ ]ₛ) * ϕ
    ≡⟨ cong (_* ϕ) (theorem-3-7-6-b-lemma S₁ S₂ S₁~S₂) ⟩
  (A′ [ S₂ ]ₛ) * ϕ
    ≡⟨ sym (lemma-3-7-5 ϕ) ⟩
  (A′ * (ϕ [ S₂ ]))
    ∎

unit-structure : Bool → FiniteStructure 1
unit-structure b 0 (s≤s z≤n) = b
unit-structure b 1 (s≤s ())

1-structure-is-true-or-false
  : (A : FiniteStructure 1)
  → A ≡ unit-structure false ⊎ A ≡ unit-structure true
1-structure-is-true-or-false A with A ℕ.zero (s≤s z≤n) ≟ false
1-structure-is-true-or-false A | yes prf =
  inj₁ (funExt λ p → funExt (λ x → lemma p x))
  where
    lemma
      : (p : ℕ)
      → (x : suc p Data.Nat.≤ 1)
      → A p x ≡ unit-structure false p x
    lemma ℕ.zero (s≤s z≤n) = prf
    lemma (suc p) (s≤s ())
1-structure-is-true-or-false A | no prf′ with ¬f→t prf′
1-structure-is-true-or-false A | no prf′ | prf =
  inj₂ (funExt λ p → funExt (λ x → lemma p x))
  where
    lemma
      : (p : ℕ)
      → (x : suc p Data.Nat.≤ 1)
      → A p x ≡ unit-structure true p x
    lemma ℕ.zero (s≤s z≤n) = prf
    lemma (suc p) (s≤s ())

weaken-struct
  : ∀ n
  → (Structure (finite-signature (suc n)))
  → (Structure (finite-signature n))
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

data Table : ℕ → Set where
  constant : Bool → Table 0
  branch
    : ∀ {n}
    → Table n
      -- ^ true branch
    → Table n
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

strengthen-struct-reduce
  : ∀ n b A p prf
  → strengthen-struct n b A p (≤-step prf) ≡ A p prf
strengthen-struct-reduce n b A p prf with p <? n
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
strengthen-struct-true n b A′ with suc n <? suc n
... | yes s-n<s-n = ⊥-elim (<-irrefl refl s-n<s-n)
... | no _ = refl

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

get-table : ∀ {n} → LP (finite-signature n) → Table n
get-table {0} ψ = constant (empty-structure * ψ)
get-table {suc _} ψ = fun→table (_* ψ)

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

gen-structs : ∀ n → List (Vec Bool n)
gen-structs 0 = L.[ V.[] ]
gen-structs (suc n) =
  (L.map (true V.∷_) (gen-structs n))
    L.++ (L.map (false V.∷_) (gen-structs n))

gen-structs-test
  : gen-structs 2
  ≡ (true  V.∷ true  V.∷ V.[]) List.∷
    (true  V.∷ false V.∷ V.[]) List.∷
    (false V.∷ true  V.∷ V.[]) List.∷
    (false V.∷ false V.∷ V.[]) List.∷ List.[]
gen-structs-test = refl

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
in-concat {ys = ys} {zs = zs} (inj₂ prf) = in-concat-comm ind-hyp
  where
    ind-hyp : _ L.∈ zs L.++ ys
    ind-hyp = in-concat {ys = zs} {zs = ys} (inj₁ prf)
{-
in-concat {ys = ys} {.(_ List.∷ _)} (inj₂ (L.here prf)) rewrite prf =
  {!L.here refl!}
in-concat {ys = ys} {.(_ List.∷ _)} (inj₂ (L.there prf)) =
  {!L.there (in-concat (inj₂ prf))!}
  -}

gen-structs-gens-all : ∀ {n} (v : Vec Bool n) → v L.∈ gen-structs n
gen-structs-gens-all V.[] = L.here refl
gen-structs-gens-all (false V.∷ xs) = {!!}
  where
    ind-hyp : xs L.∈ gen-structs _
    ind-hyp = gen-structs-gens-all xs
gen-structs-gens-all (true V.∷ xs) = {!!}

{-
_ : ∀ {n} → Table n ≡ (Vec Bool n → Bool)
_ = {!!}
-}

get-trues
  : ∀ {n}
  → (f : Vec Bool n → Bool)
  → List (Σ[ v ∈ Vec Bool n ] f v ≡ true)
get-trues = {!!}

_ : ∀ {n} → FiniteStructure n ≡ Vec Bool n
_ = {!!}

vec→fin-struct : ∀ {n} → Vec Bool n → FiniteStructure n
vec→fin-struct = {!!}

_ : ∀ {n} → (FiniteStructure n → Bool) ≡ (Vec Bool n → Bool)
_ = {!!}

_ : ∀ {n} → (FiniteStructure n → Bool) ≡ Table n
_ = {!!}

weaken-prop : ∀ {n} → LP (finite-signature n) → LP (finite-signature (suc n))
weaken-prop ⊥′ = ⊥′
weaken-prop (var p prf) = var p (≤-step prf)
weaken-prop (¬′ ψ) = ¬′ weaken-prop ψ
weaken-prop (ψ₁ ∧′ ψ₂) = weaken-prop ψ₁ ∧′ weaken-prop ψ₂
weaken-prop (ψ₁ ∨′ ψ₂) = weaken-prop ψ₁ ∨′ weaken-prop ψ₂
weaken-prop (ψ₁ →′ ψ₂) = weaken-prop ψ₁ →′ weaken-prop ψ₂
weaken-prop (ψ₁ ↔′ ψ₂) = weaken-prop ψ₁ ↔′ weaken-prop ψ₂

struct→formula
  : ∀ {n}
  → Vec Bool n
  → LP (finite-signature n)
struct→formula V.[] = ⊥′ →′ ⊥′
struct→formula {suc n} (false V.∷ V.[]) = ¬′ var n (s≤s z≤n)
struct→formula {suc n} (true V.∷ V.[]) = var n (s≤s z≤n)
struct→formula {suc (suc n)} (false V.∷ xs@(_ V.∷ _)) =
  (¬′ var (suc n) ≤-refl) ∧′ weaken-prop (struct→formula xs)
struct→formula {suc (suc n)} (true V.∷ xs@(_ V.∷ _)) =
  (var (suc n) ≤-refl) ∧′ weaken-prop (struct→formula xs)

table→formula
  : ∀ {n}
  → (Vec Bool n → Bool)
  → LP (finite-signature n)
table→formula {n} t = formula
  where
    structs : List (Vec Bool n)
    structs = gen-structs n

    filtered-structs : List (Vec Bool n)
    filtered-structs = L.boolFilter t structs

    formulas : List (LP (finite-signature n))
    formulas = L.map struct→formula filtered-structs

    formula : LP (finite-signature n)
    formula = L.foldr _∨′_ ⊥′ formulas

table→formula-test
  : table→formula
      {2}
      (table→fun-vec
        (branch
          (branch
            (constant true)
            (constant false)
          )
          (branch
            (constant true)
            (constant false)
          )
        )
      )
  ≡ (((var 1 ≤-refl) ∧′ (var 0 (≤-step (s≤s z≤n))))
      ∨′ (((¬′ var 1 ≤-refl) ∧′ var 0 (≤-step (s≤s z≤n)))
      ∨′ ⊥′)
    )
table→formula-test = refl

table→formula→table
  : ∀ {n} (t : Table n)
  → get-table (table→formula (table→fun-vec t)) ≡ t
table→formula→table (constant x) = {!!}
table→formula→table (branch t t₁) = {!!}

DNF-posts-theorem-on-tables
  : ∀ {n}
  → (t : Table n)
  → Σ[ ψ ∈ LP (finite-signature n) ] get-table ψ ≡ t
DNF-posts-theorem-on-tables t =
  table→formula (table→fun-vec t)
    , table→formula→table t

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

{-
get-truths
  : ∀ {n}
  → (t : Table n)
  → (ψ : LP (finite-signature n))
  → Σ[ v ∈ List (Vec Bool n) ]
    All (λ V → vec→fin-struct V * ψ ≡ true) v
  × ∀ A → A * ψ ≡ true → ∃! _≡_ λ i → fin-struct→vec A [ i ]=
get-truths (constant false) ψ = {!!}
get-truths (constant true) ψ = {!!}
get-truths (branch t t₁) ψ = {!!}
-}

get-truths
  : ∀ {n}
  → (t : Table n)
  → (ψ : LP (finite-signature n))
  → List (Vec Bool n)
get-truths = {!!}

posts-theorem-on-tables
  : ∀ {n}
  → (t : Table n)
  → Σ[ ψ ∈ LP (finite-signature n) ] get-table ψ ≡ t
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
      fun→table
        (_*
          ((var n ≤-refl ∧′ weaken-prop ψ₁)
          ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
        )
    ≡⟨⟩
      branch
        (fun→table
          (weaken-struct-fun
            _
            (_*
              ((var n ≤-refl ∧′ weaken-prop ψ₁)
              ∨′ ((¬′ var n ≤-refl) ∧′ weaken-prop ψ₂))
            )
            true
          )
        )
        (fun→table
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
          (λ a b → branch (fun→table a) (fun→table b))
          (funExt λ A′ → weaken-fun-disj n ψ₁ ψ₂ A′ true)
          (funExt λ A′ → weaken-fun-disj n ψ₁ ψ₂ A′ false)
    ⟩
      branch
        (fun→table (_* ψ₁))
        (fun→table (_* ψ₂))
    ≡⟨ cong₂ branch prf₁ prf₂ ⟩
      branch t₁ t₂
    ∎
  )

constant-inj
  : ∀ {a b}
  → constant a ≡ constant b
  → a ≡ b
constant-inj refl = refl

get-table-fun→table
  : ∀ n (ψ : LP (finite-signature n)) g
  → get-table ψ ≡ fun→table g
  → (_* ψ) ≡ g
get-table-fun→table ℕ.zero ψ g prf =
  funExt helper₂
  where
    helper₁ : (empty-structure * ψ) ≡ g empty-structure
    helper₁ = constant-inj prf

    helper₂ : ∀ p → (p * ψ) ≡ g p
    helper₂ p rewrite isContr-FiniteStructure-0 p = helper₁
get-table-fun→table (suc n) ψ g prf =
  funExt {!!}
  where
    ind₁ = get-table-fun→table n {!ψ!} {!!} {!!}

{-
Theorem 3.8.4
-}
posts-theorem
  : (n : ℕ)
  → let σ = finite-signature n
  in (g : Structure σ → Bool)
  → Σ[ ψ ∈ LP σ ]  _* ψ ≡ g
posts-theorem n g with posts-theorem-on-tables (fun→table g)
... | ψ , prf = ψ , get-table-fun→table n ψ g prf

{-
data IsBasicFormula (_·_ : LP σ → LP σ → LP σ) : LP σ → Set₁ where
  isBasic-lit : ∀ p prf → IsBasicFormula _·_ (var p prf)
  isBasic-fun : ∀ p prf → IsBasicFormula _·_ ψ → IsBasicFormula _·_ (var p prf · ψ)

IsBasicConjunction : LP σ → Set₁
IsBasicConjunction = IsBasicFormula _∨′_

IsBasicDisjunction : LP σ → Set₁
IsBasicDisjunction = IsBasicFormula _∧′_
-}

data IsLiteral {σ} : LP σ → Set₁ where
  isLit-var : ∀ {p prf} → IsLiteral (var p prf)
  isLit-neg-var : ∀ {p prf} → IsLiteral (¬′ var p prf)

data IsBasicConjunction : LP σ → Set₁ where
  isConj-lit : IsLiteral ψ → IsBasicConjunction ψ
  isConj-conj : IsLiteral ψ → IsBasicConjunction ϕ → IsBasicConjunction (ψ ∧′ ϕ)

data IsBasicDisjunction {σ} : LP σ → Set₁ where
  isDisj-lit : IsLiteral ψ → IsBasicDisjunction ψ
  isDisj-disj : IsLiteral ψ → IsBasicDisjunction ϕ → IsBasicDisjunction (ψ ∨′ ϕ)

data IsDNF : LP σ → Set₁ where
  isDNF-conj : IsBasicConjunction ψ → IsDNF ψ
  isDNF-disj : IsBasicConjunction ψ → IsDNF ϕ → IsDNF (ψ ∨′ ϕ)

data IsCNF : LP σ → Set₁ where
  isCNF-disj : IsBasicDisjunction ψ → IsCNF ψ
  isCNF-conj : IsBasicDisjunction ψ → IsCNF ϕ → IsCNF (ψ ∧′ ϕ)

module example-3-8-7 where
  ex₁ : LP (finite-signature 1)
  ex₁ = var 0 (s≤s z≤n) ∧′ (¬′ var 0 (s≤s z≤n))

  ex₁-prf₁ : IsDNF ex₁
  ex₁-prf₁ = isDNF-conj (isConj-conj isLit-var (isConj-lit isLit-neg-var))

  ex₁-prf₂ : IsCNF ex₁
  ex₁-prf₂ =
    isCNF-conj
      (isDisj-lit isLit-var)
      (isCNF-disj (isDisj-lit isLit-neg-var))

{-
I need to prove Post's Theorem in a different way to prove this.
-}

get-CNF : ∀ (ψ : LP σ) → Σ[ ϕ ∈ LP σ ] (IsCNF ϕ × ψ ~ ψ)
get-CNF ψ = {!!}

get-DNF : ∀ (ψ : LP σ) → Σ[ ϕ ∈ LP σ ] (IsDNF ϕ × ψ ~ ψ)
get-DNF ψ = {!!}
