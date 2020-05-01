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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
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

_*_ : ∀ {σ} → Structure σ → LP σ → Bool
f * ⊥′ = false
f * var p {prf} = f p {prf}
f * (¬′ χ) = not (f * χ)
f * (χ₁ ∧′ χ₂) = (f * χ₁) ∧ (f * χ₂)
f * (χ₁ ∨′ χ₂) = (f * χ₁) ∨ (f * χ₂)
f * (χ₁ →′ χ₂) = (f * χ₁) ⇒ (f * χ₂)
  where
    _⇒_ : Bool → Bool → Bool
    true ⇒ false = false
    _ ⇒ _ = true
f * (χ₁ ↔′ χ₂) = (f * χ₁) ⇔′ (f * χ₂)
  where
    _⇔′_ : Bool → Bool → Bool
    true ⇔′ true = true
    false ⇔′ false = true
    _ ⇔′ _ = false

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
Substitution : (σ : Signature) → (τ : Signature) → Decidable τ → τ ⊆ σ → Set
Substitution σ τ _ _ = (p : ℕ) → p ∈ τ → LP σ

subst : ∀ {σ τ} (is-in : Decidable τ) (τ⊆σ : τ ⊆ σ) → LP σ → Substitution σ τ (is-in) (τ⊆σ) → LP σ
subst _ _ ⊥′ S = ⊥′
subst is-in τ⊆σ (var p {p₁}) S with is-in p
... | yes prf = S p prf
... | no _ = var p {p₁}
subst is-in τ⊆σ (¬′ ϕ) S = ¬′ (subst is-in τ⊆σ ϕ S )
subst is-in τ⊆σ (ϕ₁ ∧′ ϕ₂) S = subst is-in τ⊆σ ϕ₁ S ∧′ subst is-in τ⊆σ ϕ₂ S
subst is-in τ⊆σ (ϕ₁ ∨′ ϕ₂) S = subst is-in τ⊆σ ϕ₁ S ∨′ subst is-in τ⊆σ ϕ₂ S
subst is-in τ⊆σ (ϕ₁ →′ ϕ₂) S = subst is-in τ⊆σ ϕ₁ S →′ subst is-in τ⊆σ ϕ₂ S
subst is-in τ⊆σ (ϕ₁ ↔′ ϕ₂) S = subst is-in τ⊆σ ϕ₁ S ↔′ subst is-in τ⊆σ ϕ₂ S

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

  p₀ p₁ p₂ p₃ : LP σ
  p₀ = var 0 {s≤s z≤n}
  p₁ = var 1 {s≤s (s≤s z≤n)}
  p₂ = var 2 {s≤s (s≤s (s≤s z≤n))}
  p₃ = var 3 {s≤s (s≤s (s≤s (s≤s z≤n)))}

  ϕ : LP σ
  ϕ = (p₁ →′ (p₂ ∧′ (¬′ p₃))) ↔′ p₃

  ψ₁ ψ₂ ψ₃ : LP σ
  ψ₁ = ¬′ (¬′ p₃)
  ψ₂ = p₀
  ψ₃ = p₁ →′ p₂

  S : Substitution σ τ τ-dec proj₂
  S 0 ()
  S (suc 0) _ = ψ₁
  S (suc (suc 0)) _ = ψ₂
  S (suc (suc (suc 0))) _ = ψ₃
  S (suc (suc (suc (suc _)))) (_ , s≤s (s≤s (s≤s (s≤s ()))))

  ϕ′ : LP σ
  ϕ′ = subst τ-dec proj₂ ϕ S

  _ : ϕ′ ≡ (((¬′ (¬′ p₃)) →′ (p₀ ∧′ (¬′ (p₁ →′ p₂)))) ↔′
              (p₁ →′ p₂))
  _ = refl
