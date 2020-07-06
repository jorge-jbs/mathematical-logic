{-# OPTIONS --without-K #-}

open import Level using (0ℓ; _⊔_)
open import Axiom.Extensionality.Propositional using (Extensionality)

module Examples (funExt : Extensionality 0ℓ 0ℓ) where

open import Data.Nat using (ℕ; suc; _<_; _<?_; _>_; _>?_; z≤n; s≤s)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Bool
  using (Bool; false; true; _≟_; not; _∧_; _∨_; if_then_else_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Unary
  using (Decidable; _∪_; _⊆_)
  renaming (｛_｝ to ⟦_⟧)
open import Relation.Nullary using (¬_; yes; no)

open import PropositionalLogic funExt
open import Signature
open import Structure funExt
open import Derivation funExt

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

example-2-4-5
  : ∀ {σ} (ϕ ψ χ : LP σ)
  → (⟦ ϕ →′ ψ ⟧ ∪ ⟦ ψ →′ χ ⟧) ⊢ (ϕ →′ χ)
example-2-4-5 ϕ ψ χ =
  →-intro ϕ χ  -- ϕ → χ
    (→-elim   -- χ
      (→-elim  -- ψ
        (weakening lemma₁ (axiom ϕ))  -- ϕ
        (weakening lemma₂ (axiom (ϕ →′ ψ)))  -- ϕ →′ ψ
      )
      (weakening lemma₃ (axiom (ψ →′ χ)))  -- ψ → χ
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
