{-# OPTIONS --without-K #-}

open import Level
open import Axiom.Extensionality.Propositional using (Extensionality)

module Derivation (funExt : Extensionality 0ℓ 0ℓ) where

import Level
open Level using (0ℓ)

open import Signature
open import PropositionalLogic funExt
open import Relation.Unary
  hiding (_⊢_; _∈_)
  renaming (｛_｝ to ⟦_⟧)

Assumptions : (σ : Signature) → Set₂
Assumptions σ = Pred (LP σ) (Level.suc 0ℓ)

private
  variable
    σ : Signature
    ψ ϕ χ : LP σ
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
