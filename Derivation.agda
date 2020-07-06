{-# OPTIONS --without-K #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Axiom.ExcludedMiddle

module Derivation (funExt : Extensionality 0ℓ 0ℓ) where

open import Data.Empty
open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Unary
  hiding (_⊢_; _∈_)
  renaming (｛_｝ to ⟦_⟧)

open import Signature
open import Structure funExt
open import PropositionalLogic funExt
open import Utils

Assumptions : (σ : Signature) → Set₂
Assumptions σ = Pred (LP σ) (Level.suc 0ℓ)

private
  variable
    σ : Signature
    ψ ϕ χ : LP σ
    A : Structure σ
    Γ Γ′ Δ Δ′ : Assumptions σ

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
  ∧-intro
    : Γ     ⊢ ϕ
    → Δ     ⊢ ψ
    → Γ ∪ Δ ⊢ ϕ ∧′ ψ
  ∧-elim₁
    : Γ ⊢ ϕ ∧′ ψ
    → Γ ⊢ ϕ
  ∧-elim₂
    : Γ ⊢ ϕ ∧′ ψ
    → Γ ⊢ ψ
  →-intro
    : Γ ∪ ⟦ ϕ ⟧ ⊢ ψ
    → Γ         ⊢ ϕ →′ ψ
  →-elim
    : Γ     ⊢ ϕ
    → Δ     ⊢ ϕ →′ ψ
    → Γ ∪ Δ ⊢ ψ
  ↔-intro
    : Γ     ⊢ ϕ →′ ψ
    → Δ     ⊢ ψ →′ ϕ
    → Γ ∪ Δ ⊢ ϕ ↔′ ψ
  ↔-elim₁
    : Γ ⊢ ϕ ↔′ ψ
    → Γ ⊢ ϕ →′ ψ
  ↔-elim₂
    : Γ ⊢ ϕ ↔′ ψ
    → Γ ⊢ ψ →′ ϕ
  ¬-intro
    : Γ ∪ ⟦ ϕ ⟧ ⊢ ⊥′
    → Γ         ⊢ ¬′ ϕ
  ¬-elim
    : Γ     ⊢ ϕ
    → Δ     ⊢ ¬′ ϕ
    → Γ ∪ Δ ⊢ ⊥′
  RAA
    : Γ ∪ ⟦ ¬′ ϕ ⟧ ⊢ ⊥′
    → Γ            ⊢ ϕ
  ∨-intro₁
    : Γ ⊢ ϕ
    → Γ ⊢ ϕ ∨′ ψ
  ∨-intro₂
    : Γ ⊢ ψ
    → Γ ⊢ ϕ ∨′ ψ
  ∨-elim
    : Γ ∪ ⟦ ϕ ⟧ ⊢ χ
    → Δ ∪ ⟦ ψ ⟧ ⊢ χ
    → Γ ∪ Δ ∪ ⟦ ϕ ∨′ ψ ⟧ ⊢ χ

_⊬_ : Assumptions σ → LP σ → Set₂
Γ ⊬ ϕ = ¬ (Γ ⊢ ϕ)

IsModel : Structure σ → Assumptions σ → Set₁
IsModel A Γ = ∀ ϕ → ϕ ∈ Γ → A * ϕ ≡ true

_⊨_ : Assumptions σ → LP σ → Set₁
Γ ⊨ ϕ = ∀ A → IsModel A Γ → A * ϕ ≡ true

_⊭_ : Assumptions σ → LP σ → Set₁
Γ ⊭ ϕ = ¬ (Γ ⊨ ϕ)

Soundness : Set₂
Soundness =
  ∀ {σ} {Γ : Assumptions σ} ψ
  → Γ ⊢ ψ → Γ ⊨ ψ

Adequacy : Set₂
Adequacy =
  ∀ {σ} {Γ : Assumptions σ} ψ
  → Γ ⊨ ψ → Γ ⊢ ψ

Completeness : Set₂
Completeness = Soundness × Adequacy

IsConsistent : Assumptions σ → Set₂
IsConsistent Γ = Γ ⊬ ⊥′

--has-model→consistent : IsModel A Γ → IsConsistent Γ
--has-model→consistent = {!!}

model⊆ : IsModel A Δ → Γ ⊆ Δ → IsModel A Γ
model⊆ = {!!}

model∪₁ : IsModel A (Γ ∪ Δ) → IsModel A Γ
model∪₁ = {!!}

model∪₂ : IsModel A (Γ ∪ Δ) → IsModel A Δ
model∪₂ = {!!}

model∪ : IsModel A Γ → IsModel A Δ → IsModel A (Γ ∪ Δ)
model∪ = {!!}

model-singl : IsModel A ⟦ ψ ⟧ → A * ψ ≡ true
model-singl {ψ = ψ} model = model ψ refl

model-singl-inv : A * ψ ≡ true → IsModel A ⟦ ψ ⟧
model-singl-inv prf ψ refl = prf

∨-helper : ∀ {a b} → a ∨ b ≡ true → (a ≡ true) ⊎ (b ≡ true)
∨-helper {false} {b} prf = inj₂ prf
∨-helper {true} {b} prf = inj₁ prf

model∨ : A * (ϕ ∨′ ψ) ≡ true → ((A * ϕ ≡ true) ⊎ (A * ψ ≡ true))
model∨ {A = A} {ϕ = ϕ} {ψ = ψ} prf = ∨-helper lemma
  where
    lemma : (A * ϕ) ∨ (A * ψ) ≡ true
    lemma = prf

∧-helper₁ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-helper₁ {a = true} refl = refl

∧-helper₂ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-helper₂ {a = true} refl = refl

⇒b-cancel-left : ∀ {a} → false ⇒b a ≡ true
⇒b-cancel-left {false} = refl
⇒b-cancel-left {true} = refl

⇒b-left-identity : ∀ {a} → true ⇒b a ≡ a
⇒b-left-identity {false} = refl
⇒b-left-identity {true} = refl

sound : Soundness
sound ψ (weakening subset D) A model = sound ψ D A (model⊆ model subset)
sound ψ (axiom ψ) A model = model ψ refl
sound ψ (transitive D x) A model = {!!}
sound (ϕ ∧′ ψ) (∧-intro D₁ D₂) A model =
  let
    ind-hyp₁ = sound ϕ D₁ A (model∪₁ model)
    ind-hyp₂ = sound ψ D₂ A (model∪₂ model)
  in
    begin
        (A * ϕ) ∧ (A * ψ)
    ≡⟨ cong₂ _∧_ ind-hyp₁ ind-hyp₂ ⟩
        true ∧ true
    ≡⟨⟩
        true
    ∎
sound ψ (∧-elim₁ D) A model =
  let ind-hyp = sound _ D A model
  in ∧-helper₁ ind-hyp
sound ψ (∧-elim₂ D) A model =
  let ind-hyp = sound _ D A model
  in ∧-helper₂ ind-hyp
sound (ϕ →′ ψ) (→-intro D) A model with A * ϕ ≟ true
... | yes prf =
  let
    ind-hyp = sound ψ D A (model∪ model (model-singl-inv prf))
  in
    begin
        (A * ϕ) ⇒b (A * ψ)
    ≡⟨ cong₂ (_⇒b_) prf ind-hyp ⟩
        true ⇒b true
    ≡⟨⟩
        true
    ∎
... | no prf =
  begin
      (A * ϕ) ⇒b (A * ψ)
  ≡⟨ cong (_⇒b (A * ψ)) (¬t→f prf) ⟩
      false ⇒b (A * ψ)
  ≡⟨ ⇒b-cancel-left ⟩
      true
  ∎
sound ψ (→-elim {ϕ = ϕ} D₁ D₂) A model =
  let
    ind-hyp₁ : A * ϕ ≡ true
    ind-hyp₁ = sound ϕ D₁ A (λ ϕ z → model ϕ (inj₁ z))

    ind-hyp₂ : A * (ϕ →′ ψ) ≡ true
    ind-hyp₂ = sound (ϕ →′ ψ) D₂ A (λ ϕ z → model ϕ (inj₂ z))

  in
    begin
        A * ψ
    ≡⟨ sym ⇒b-left-identity ⟩
        true ⇒b (A * ψ)
    ≡⟨ cong (_⇒b (A * ψ)) (sym ind-hyp₁) ⟩
        (A * ϕ) ⇒b (A * ψ)
    ≡⟨ ind-hyp₂ ⟩
        true
    ∎
sound (ϕ ↔′ ψ) (↔-intro D₁ D₂) A model = {!!}
sound (_ →′ _) (↔-elim₁ D) A x₁ = {!!}
sound (_ →′ _) (↔-elim₂ D) A x₁ = {!!}
sound (¬′ _) (¬-intro D) A x₁ = {!!}
sound ⊥′ (¬-elim D D₁) A x₁ = {!!}
sound ψ (RAA D) A x₁ = {!!}
sound (ϕ ∨′ ψ) (∨-intro₁ D) A model =
  let ind-hyp = sound ϕ D A model
  in
    begin
        (A * ϕ) ∨ (A * ψ)
    ≡⟨ cong (_∨ (A * ψ)) ind-hyp ⟩
        true ∨ (A * ψ)
    ≡⟨⟩
        true
    ∎
sound (ϕ ∨′ ψ) (∨-intro₂ D) A model =
  let ind-hyp = sound ψ D A model
  in
    begin
        (A * ϕ) ∨ (A * ψ)
    ≡⟨ cong ((A * ϕ) ∨_) ind-hyp ⟩
        (A * ϕ) ∨ true
    ≡⟨ ∨-comm (A * ϕ) true ⟩
        true ∨ (A * ϕ)
    ≡⟨⟩
        true
    ∎
sound χ (∨-elim {Γ = Γ}{ϕ = ϕ}{Δ = Δ}{ψ = ψ} D₁ D₂) A model
  with
    model∨ {A = A} {ϕ = ϕ} {ψ = ψ}
      (model-singl (model∪₂ (model∪₂ model)))
... | inj₁ prf =
  let
    model′ : IsModel A (Γ ∪ ⟦ ϕ ⟧)
    model′ = model∪ (model∪₁ model) (model-singl-inv prf)

    ind-hyp : A * χ ≡ true
    ind-hyp = sound χ D₁ A model′

  in ind-hyp
... | inj₂ prf =
  let
    model′ : IsModel A (Δ ∪ ⟦ ψ ⟧)
    model′ = model∪ (model∪₁ (model∪₂ model)) (model-singl-inv prf)

    ind-hyp : A * χ ≡ true
    ind-hyp = sound χ D₂ A model′

  in ind-hyp

{-
Lemma 3.10.3
-}
consistent→model→adequacy
  : (∀ (Γ : Assumptions σ) → IsConsistent Γ → ∃[ A ] IsModel A Γ)
  → Adequacy
consistent→model→adequacy = {!!}

{-
Definition 3.10.4
-}
record IsHintikka (Γ : Assumptions σ) : Set₁ where
  field
    and : (ϕ ∧′ ψ) ∈ Γ → ϕ ∈ Γ × ψ ∈ Γ
    or : (¬′ (ϕ ∧′ ψ)) ∈ Γ → ¬′ ϕ ∈ Γ ⊎ ¬′ ψ ∈ Γ
    neg : (¬′ ¬′ ϕ) ∈ Γ → ϕ ∈ Γ
    bot : ⊥′ ∉ Γ
    vars : ∀ p prf → ¬ (var p prf ∈ Γ × ¬′ var p prf ∈ Γ)

bool-DeMorgan-∧ : ∀ {a b} → not (a ∧ b) ≡ not a ∨ not b
bool-DeMorgan-∧ {false} {b} = refl
bool-DeMorgan-∧ {true} {b} = refl

DeMorgan-∧ : (¬′ (ϕ ∧′ ψ)) ~ ((¬′ ϕ) ∨′ (¬′ ψ))
DeMorgan-∧ {ϕ = ϕ}{ψ = ψ} A =
  begin
      A * (¬′ (ϕ ∧′ ψ))
  ≡⟨⟩
      not (A * ϕ ∧ A * ψ)
  ≡⟨ bool-DeMorgan-∧ {A * ϕ} {A * ψ} ⟩
      not (A * ϕ) ∨ not (A * ψ)
  ≡⟨⟩
      A * ((¬′ ϕ) ∨′ (¬′ ψ))
  ∎

bool-DeMorgan-∨ : ∀ {a b} → not (a ∨ b) ≡ not a ∧ not b
bool-DeMorgan-∨ {false} {b} = refl
bool-DeMorgan-∨ {true} {b} = refl

DeMorgan-∨ : (¬′ (ϕ ∨′ ψ)) ~ ((¬′ ϕ) ∧′ (¬′ ψ))
DeMorgan-∨ {ϕ = ϕ}{ψ = ψ} A =
  begin
      A * (¬′ (ϕ ∨′ ψ))
  ≡⟨⟩
      not (A * ϕ ∨ A * ψ)
  ≡⟨ bool-DeMorgan-∨ {A * ϕ} {A * ψ} ⟩
      not (A * ϕ) ∧ not (A * ψ)
  ≡⟨⟩
      A * ((¬′ ϕ) ∧′ (¬′ ψ))
  ∎

IsBasic : LP σ → Set
IsBasic ⊥′ = ⊤
IsBasic (var _ _) = ⊤
IsBasic (¬′ ϕ) = IsBasic ϕ
IsBasic (ϕ ∧′ ψ) = IsBasic ϕ × IsBasic ψ
IsBasic (_ ∨′ _) = ⊥
IsBasic (_ →′ _) = ⊥
IsBasic (_ ↔′ _) = ⊥

AreBasicAssumptions : Assumptions σ → Set₁
AreBasicAssumptions Γ = ∀ ϕ → ϕ ∈ Γ → IsBasic ϕ

{-
_
  :
  → IsConsistent Γ
  → Dec (IsConsistent (Γ ∪ ⟦ χ ⟧))
  -- ~ Dec (Γ ⊢ χ)
-}

{-
Lemma 3.10.5

We add the precondition that Γ is decidable since we don't have LEM.
-}
hintikka-has-model
  : ∀ {σ}{Γ : Assumptions σ}
  → Decidable Γ
  → AreBasicAssumptions Γ
  → IsHintikka Γ
  → ∃[ A ] IsModel A Γ
hintikka-has-model {σ = σ}{Γ = Γ} dec-Γ is-basic is-hintikka =
  B , a
  where
    B : Structure σ
    B p prf with dec-Γ (var p prf)
    ... | yes _ = true
    ... | no _ = false

    a : ∀ ϕ → ϕ ∈ Γ → B * ϕ ≡ true
    b : ∀ ϕ → ¬′ ϕ ∈ Γ → B * ϕ ≡ false

    b→a : ∀ ϕ → B * ϕ ≡ false →  B * (¬′ ϕ) ≡ true
    b→a ϕ prf =
      begin
          B * (¬′ ϕ)
      ≡⟨⟩
          not (B * ϕ)
      ≡⟨ cong not prf ⟩
          not false
      ≡⟨⟩
          true
      ∎

    a ⊥′ prf = ⊥-elim (IsHintikka.bot is-hintikka prf)
    a (var p prf′) prf with dec-Γ (var p prf′)
    ... | yes _ = refl
    ... | no ¬prf = ⊥-elim (¬prf prf)
    a (¬′ ϕ) prf = b→a ϕ (b ϕ prf)
    a (ϕ ∧′ ψ) prf =
      let
        ϕ-prf , ψ-prf = IsHintikka.and is-hintikka prf
        ind-hyp₁ = a ϕ ϕ-prf
        ind-hyp₂ = a ψ ψ-prf
      in
        begin
            B * (ϕ ∧′ ψ)
        ≡⟨⟩
            B * ϕ ∧ B * ψ
        ≡⟨ cong₂ _∧_ ind-hyp₁ ind-hyp₂ ⟩
            true
        ∎
    a ϕ@(_ ∨′ _) prf = ⊥-elim (is-basic ϕ prf)
    a ϕ@(_ →′ _) prf = ⊥-elim (is-basic ϕ prf)
    a ϕ@(_ ↔′ _) prf = ⊥-elim (is-basic ϕ prf)

    b ⊥′ prf = refl
    b (var p prf′) prf₁ with dec-Γ (var p prf′)
    ... | yes prf₂ =
      ⊥-elim (IsHintikka.vars is-hintikka p prf′ (prf₂ , prf₁))
    ... | no _ = refl
    b (¬′ ϕ) prf =
      let
        ind-hyp : (B * ϕ) ≡ true
        ind-hyp = a ϕ (IsHintikka.neg is-hintikka prf)
      in
        begin
            B * (¬′ ϕ)
        ≡⟨⟩
            not (B * ϕ)
        ≡⟨ cong not ind-hyp ⟩
            not true
        ≡⟨⟩
            false
        ∎
    b (ϕ ∧′ ψ) prf with IsHintikka.or is-hintikka prf
    ... | inj₁ prf₁ =
      let
        ind-hyp : B * ϕ ≡ false
        ind-hyp = b ϕ prf₁
      in
        begin
            B * (ϕ ∧′ ψ)
        ≡⟨⟩
            B * ϕ ∧ B * ψ
        ≡⟨ cong (_∧ B * ψ) ind-hyp ⟩
            false ∧ B * ψ
        ≡⟨⟩
            false
        ∎
    ... | inj₂ prf₂ =
      let
        ind-hyp : B * ψ ≡ false
        ind-hyp = b ψ prf₂
      in
        begin
            B * (ϕ ∧′ ψ)
        ≡⟨⟩
            B * ϕ ∧ B * ψ
        ≡⟨ cong (B * ϕ ∧_) ind-hyp ⟩
            B * ϕ ∧ false
        ≡⟨ ∧-comm (B * ϕ) false ⟩
            false ∧ B * ϕ
        ≡⟨⟩
            false
        ∎
    b ϕ@(_ ∨′ _) prf = ⊥-elim (is-basic (¬′ ϕ) prf)
    b ϕ@(_ →′ _) prf = ⊥-elim (is-basic (¬′ ϕ) prf)
    b ϕ@(_ ↔′ _) prf = ⊥-elim (is-basic (¬′ ϕ) prf)

module _ (lem : ExcludedMiddle 0ℓ) where

  {-
  Lemma 3.10.6
  -}
  consistent→hintikka
    : ∀ {Γ : Assumptions σ}
    → IsConsistent Γ
    → AreBasicAssumptions Γ
    → Σ[ Δ ∈ Assumptions σ ] IsHintikka Δ × Γ ⊆ Δ
  consistent→hintikka consistent is-basic = {!!}

  consistent-have-models→adequacy
    : (∀ (Γ : Assumptions σ) → IsConsistent Γ → ∃[ A ] IsModel A Γ)
    → Adequacy
  consistent-have-models→adequacy x ψ get-model = {!!}

  adequate : Adequacy
  adequate = consistent→model→adequacy
    λ Γ cons → hintikka-has-model
      {!!}
      {!!}
      (proj₁ (proj₂ (consistent→hintikka cons {!!})))
