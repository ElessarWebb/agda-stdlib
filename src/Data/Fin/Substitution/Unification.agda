open import Data.Nat
open import Relation.Unary
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas using (AppLemmas)

module Data.Fin.Substitution.Unification {ℓ} {T₁ : Pred ℕ ℓ} (app : Application T₁ T₁) where

open import Data.Product
open import Data.Fin as Fin
open import Data.Vec
open import Relation.Nullary

open Application app

open import Relation.Binary.PropositionalEquality as P
open P.≡-Reasoning

{- Unifiers -}
module _ where
  IsUnifier : ∀ {n m} (φ : Sub T₁ n m) t₁ t₂ → Set ℓ
  IsUnifier φ t₁ t₂ = t₁ / φ ≡ t₂ / φ

  _≈⟨_⟩_ : ∀ {n m} → T₁ n → Sub T₁ n m → T₁ n → Set ℓ
  t₁ ≈⟨ φ ⟩ t₂ = IsUnifier φ t₁ t₂

  record Unifier {n} t₁ t₂ : Set ℓ where
    constructor unify
    field
      {m}       : ℕ
      unifier   : Sub T₁ n m 
      unifies   : IsUnifier unifier t₁ t₂

  _≈≈_ : ∀ {n} → T₁ n → T₁ n → Set ℓ
  t₁ ≈≈ t₂ = Unifier t₁ t₂

  _≈/≈_ : ∀ {n} → T₁ n → T₁ n → Set ℓ
  t₁ ≈/≈ t₂ = ¬ (t₁ ≈≈ t₂)

{- Most general unifiers -}
module _ where
  record IsMGU {n m} (φ : Sub T₁ n m) t₁ t₂ : Set ℓ where
    field
      unifies   : IsUnifier φ t₁ t₂
      minimal   : ∀ {m'} (θ : Sub T₁ n m') → t₁ / θ ≡ t₂ / θ → ∃ λ ψ → θ ≡ φ ⊙ ψ

    unifier : Unifier t₁ t₂
    unifier = record { unifies = unifies }

  record MGU {n} t₁ t₂ : Set ℓ where
    constructor mgu
    field
      {m}    : ℕ
      φ      : Sub T₁ n m
      isMGU  : IsMGU φ t₁ t₂

    open IsMGU isMGU public
