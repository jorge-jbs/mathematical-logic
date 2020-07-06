{-# OPTIONS --without-K --safe #-}

module Signature where

open import Level
open import Data.Nat
open import Data.Sum
open import Relation.Unary
open import Relation.Unary using (_∈_; _∉_) public
open import Relation.Nullary

Signature : Set₁
Signature = Pred ℕ 0ℓ

finite-signature : ℕ → Signature
finite-signature n = λ k → k < n

sets-lemma : ∀ {τ σ : Signature} (p : ℕ) → τ ⊆ σ → p ∈ (σ ∪ τ) → p ∈ σ
sets-lemma p τ⊆σ p∈σ∪τ with p∈σ∪τ
... | inj₁ p∈σ = p∈σ
... | inj₂ p∈τ = τ⊆σ p∈τ

