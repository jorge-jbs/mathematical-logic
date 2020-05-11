{-
Formalization of Propositional Logic following "Mathematical Logic" of
Ian Chiswell and Wilfrid Hodges.
-}

{-# OPTIONS --safe #-}

open import Agda.Builtin.Sigma using (_,_)
open import Level using (0ℓ)
open import Data.Bool using (Bool; false; true; _≟_; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Nat using (ℕ; suc; _<_; _<?_; _>_; _>?_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂; _,′_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; Equivalence; equivalence)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred; Decidable; ∅; _∪_; _⊆_) renaming (｛_｝ to ⟦_⟧)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)

max : ℕ → ℕ → ℕ
max 0 m = m
max (suc n) 0 = suc n
max (suc n) (suc m) = max n m

Signature : Set₁
Signature = Pred ℕ 0ℓ

_∈_ : (p : ℕ) (σ : Signature) → Set
p ∈ σ = σ p

data LP : (σ : Signature) → Set where
  ⊥′ : ∀ {σ} → LP σ
  var : ∀ {σ} → (p : ℕ) → {p ∈ σ} → LP σ
  ¬′_ : ∀ {σ} → LP σ → LP σ
  _∧′_ _∨′_ _→′_ _↔′_ : ∀ {σ} → LP σ → LP σ → LP σ

height : ∀ {σ} → LP σ → ℕ
height ⊥′ = 0
height (var p) = 0
height (¬′ ψ) = suc (height ψ)
height (ϕ ∧′ ψ) = max (height ϕ) (height ψ)
height (ϕ ∨′ ψ) = max (height ϕ) (height ψ)
height (ϕ →′ ψ) = max (height ϕ) (height ψ)
height (ϕ ↔′ ψ) = max (height ϕ) (height ψ)

Assumptions : (σ : Signature) → Set₁
Assumptions σ = Pred (LP σ) 0ℓ

infixr 3 _⊢_

{-
Definition 3.4.1 (σ-derivation) and 3.4.4 (σ-sequent). Merged thanks to
dependent types.
-}
data _⊢_
    : {σ : Signature}
    → (Γ : Assumptions σ)
    → (conclusion : LP σ)
    → Set₁ where
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
      _⊆_ {Level.zero} {LP σ} {Level.zero} {Level.zero}
      (⟦_⟧ {Level.zero} {LP σ} (_→′_ {σ} ψ χ))
      (_∪_ {Level.zero} {LP σ} {Level.zero} {Level.zero}
      (_∪_ {Level.zero} {LP σ} {Level.zero} {Level.zero}
      (⟦_⟧ {Level.zero} {LP σ} (_→′_ {σ} ϕ ψ))
      (⟦_⟧ {Level.zero} {LP σ} (_→′_ {σ} ψ χ)))
      (⟦_⟧ {Level.zero} {LP σ} ϕ))
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
Structure σ = (p : ℕ) → {p ∈ σ} → Bool

FiniteStructure : (n : ℕ) → Set
FiniteStructure n = Structure (λ k → k < n)

build-fin-struct : ∀ {n} → (Fin n → Bool) → FiniteStructure n
build-fin-struct f p {prf} = f (fromℕ< prf)

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
f * var p {prf} = f p {prf}
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
    var 1 {s≤s (s≤s z≤n)}
      ∧′ (¬′ (var 0 {s≤s z≤n} →′ var 2 {s≤s (s≤s (s≤s z≤n))}))

  _ : A′ * χ ≡ false
  _ = refl

{-
Definition 3.5.7 (tautology)
-}

⊨ : ∀ {σ} (ϕ : LP σ) → Set
⊨ {σ} ϕ = ∀ {A′ : Structure σ} → A′ * ϕ ≡ true

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

  ¬t→f : ∀ {b : Bool} → b ≢ true → b ≡ false
  ¬t→f {true} prf = ⊥-elim (prf refl)
  ¬t→f {false} _ = refl

  i→ii : I → II
  i→ii i-prf A′ with A′ * ϕ ≟ true | A′ * ψ ≟ true
  i→ii i-prf A′ | yes ϕ-true | yes ψ-true rewrite ϕ-true rewrite ψ-true = refl
  i→ii i-prf A′ | no ϕ-false | no ψ-false
      rewrite ¬t→f ϕ-false rewrite ¬t→f ψ-false = refl
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
Substitution : (σ : Signature) → (τ : Signature) → Set
Substitution σ τ = Decidable τ × τ ⊆ σ × ((p : ℕ) → p ∈ τ → LP σ)

sets-lemma : ∀ {σ τ} (p : ℕ) → τ ⊆ σ → p ∈ (σ ∪ τ) → p ∈ σ
sets-lemma p τ⊆σ p∈σ∪τ with p∈σ∪τ
... | inj₁ p∈σ = p∈σ
... | inj₂ p∈τ = τ⊆σ p∈τ

_[_] : ∀ {σ τ} → LP (σ ∪ τ) → Substitution σ τ → LP σ
⊥′ [ S ] = ⊥′
_[_] {σ} {τ} (var p {p∈σ∪τ}) (dec , τ⊆σ , f) with dec p
... | yes p∈τ = f p p∈τ
... | no _ = var p {sets-lemma {σ} {τ} p τ⊆σ p∈σ∪τ}
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
  p₀ = var 0 {inj₁ (s≤s z≤n)}
  p₁ = var 1 {inj₁ (s≤s (s≤s z≤n))}
  p₂ = var 2 {inj₁ (s≤s (s≤s (s≤s z≤n)))}
  p₃ = var 3 {inj₁ (s≤s (s≤s (s≤s (s≤s z≤n))))}

  p₀′ p₁′ p₂′ p₃′ : LP σ
  p₀′ = var 0 {s≤s z≤n}
  p₁′ = var 1 {s≤s (s≤s z≤n)}
  p₂′ = var 2 {s≤s (s≤s (s≤s z≤n))}
  p₃′ = var 3 {s≤s (s≤s (s≤s (s≤s z≤n)))}

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
  S = τ-dec , proj₂ , f

  ϕ′ : LP σ
  ϕ′ = ϕ [ S ]

  _ : ϕ′ ≡ (((¬′ (¬′ p₃′)) →′ (p₀′ ∧′ (¬′ (p₁′ →′ p₂′)))) ↔′
              (p₁′ →′ p₂′))
  _ = refl

{-
Definition 3.7.4
-}
_[_]ₛ : ∀ {σ τ} → Structure σ → Substitution σ τ → Structure (σ ∪ τ)
(A′ [ (dec , τ⊆σ , f) ]ₛ) p {p∈σ∪τ} with dec p
... | yes p∈τ =  A′ * (f p p∈τ)
... | no _ with p∈σ∪τ
...        | inj₁ p∈σ = A′ p {p∈σ}
...        | inj₂ p∈τ = A′ p {τ⊆σ p∈τ}

{-
Lemma 3.7.5
-}
lemma-3-7-5
  : ∀ {σ τ}
  → (A′ : Structure σ) (ϕ : LP (σ ∪ τ)) (S : Substitution σ τ)
  → A′ * (ϕ [ S ]) ≡ (A′ [ S ]ₛ) * ϕ
lemma-3-7-5 A′ ⊥′ S = refl
lemma-3-7-5 A′ (var p {p∈σ∪τ}) (∈τ , _ , _) with ∈τ p | p∈σ∪τ
lemma-3-7-5 A′ (var p {p∈σ∪τ}) (∈τ , _ , _) | yes p∈τ | _        = refl
lemma-3-7-5 A′ (var p {p∈σ∪τ}) (∈τ , _ , _) | no ¬p∈τ | inj₁ p∈σ = refl
lemma-3-7-5 A′ (var p {p∈σ∪τ}) (∈τ , _ , _) | no ¬p∈τ | inj₂ p∈τ = refl
lemma-3-7-5 A′ (¬′ ϕ) S = cong not (lemma-3-7-5 A′ ϕ S)
lemma-3-7-5 A′ (ϕ₁ ∧′ ϕ₂) S =
  cong₂ _∧_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ ∨′ ϕ₂) S =
  cong₂ _∨_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ →′ ϕ₂) S =
  cong₂ _⇒b_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
lemma-3-7-5 A′ (ϕ₁ ↔′ ϕ₂) S =
  cong₂ _⇔b_ (lemma-3-7-5 A′ ϕ₁ S) (lemma-3-7-5 A′ ϕ₂ S)
