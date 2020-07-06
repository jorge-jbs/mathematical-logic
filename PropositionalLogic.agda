{-
Formalization of Propositional Logic following "Mathematical Logic" of
Ian Chiswell and Wilfrid Hodges.
-}

--{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level using (Level; 0ℓ)
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

open import Signature
open import Structure funExt
open import Table funExt
open import Utils

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
    A B : Structure σ

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
IsTautology : (ϕ : LP σ) → Set
IsTautology ϕ = ∀ A → A * ϕ ≡ true

{-
Lemma 3.6.1
-}
module lemma-3-6-1 (ϕ ψ : LP σ) where
  I : Set
  I = ∀ A → A * ϕ ≡ true ⇔ A * ψ ≡ true

  II : Set
  II = ∀ A → A * ϕ ≡ A * ψ

  III : Set
  III = IsTautology (ϕ ↔′ ψ)

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
theorem-3-7-6-a ϕ₁ ϕ₂ S ϕ₁~ϕ₂ A′ =
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
  : (ϕ : LP (σ ∪ τ))
  → (S₁ S₂ : Substitution σ τ)
  → S₁ ~ₛ S₂
  → (ϕ [ S₁ ]) ~ (ϕ [ S₂ ])
theorem-3-7-6-b ϕ S₁ S₂ S₁~S₂ A =
  (A * (ϕ [ S₁ ]))
    ≡⟨ lemma-3-7-5 ϕ ⟩
  (A [ S₁ ]ₛ) * ϕ
    ≡⟨ cong (_* ϕ) (theorem-3-7-6-b-lemma S₁ S₂ S₁~S₂) ⟩
  (A [ S₂ ]ₛ) * ϕ
    ≡⟨ sym (lemma-3-7-5 ϕ) ⟩
  (A * (ϕ [ S₂ ]))
    ∎

get-table : ∀ {n} → LP (finite-signature n) → Table n
get-table {0} ψ = constant (empty-structure * ψ)
get-table {suc _} ψ = fun→table (_* ψ)

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
    structs = enum-vec-bool n

    filtered-structs : List (Vec Bool n)
    filtered-structs = L.boolFilter t structs

    formulas : List (LP (finite-signature n))
    formulas = L.map struct→formula filtered-structs

    formula : LP (finite-signature n)
    formula = L.foldr _∨′_ ⊥′ formulas

_
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
_ = refl

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
  → strengthen-struct n b A′ * weaken-prop ψ ≡ A′ * ψ
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
Definitions (3.8.6)
-}

data IsLiteral {σ} : LP σ → Set₁ where
  isLit-var : ∀ {p prf} → IsLiteral (var p prf)
  isLit-neg-var : ∀ {p prf} → IsLiteral (¬′ var p prf)

data IsBasicConjunction : LP σ → Set₁ where
  isConj-lit : IsLiteral ψ → IsBasicConjunction ψ
  isConj-conj : IsLiteral ψ → IsBasicConjunction ϕ → IsBasicConjunction (ψ ∧′ ϕ)

data IsBasicDisjunction : LP σ → Set₁ where
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

isDNF-table→formula
  : ∀ {n} (t : Table n)
  → IsDNF (table→formula (table→fun-vec t))
isDNF-table→formula t = {!!}

deMorgan : LP σ → LP σ
deMorgan = {!!}

module _ {n} (ψ : LP (finite-signature n)) where

  formula→table→formula : table→formula (table→fun-vec (get-table ψ)) ~ ψ
  formula→table→formula = {!!}

  get-DNF : LP (finite-signature n)
  get-DNF = proj₁ (DNF-posts-theorem-on-tables (get-table ψ))

  isDNF-get-DNF : IsDNF get-DNF
  isDNF-get-DNF = isDNF-table→formula (get-table ψ)

  equiv-get-DNF : get-DNF ~ ψ
  equiv-get-DNF = formula→table→formula

module _ {n} (ψ : LP (finite-signature n)) where

  get-CNF : LP (finite-signature n)
  get-CNF = deMorgan (¬′ get-DNF (¬′ ψ))

  isCNF-get-CNF : IsCNF get-CNF
  isCNF-get-CNF = {!!}

  equiv-get-CNF : get-CNF ~ ψ
  equiv-get-CNF = {!!}
