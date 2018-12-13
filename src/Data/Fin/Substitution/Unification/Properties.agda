open import Data.Nat
open import Data.Fin.Substitution.Lemmas

module Data.Fin.Substitution.Unification.Properties {T₁ : ℕ → Set} (lemmas : TermLemmas T₁) where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin as Fin
open import Data.Fin.Substitution using (Sub)

open ≡-Reasoning
open TermLemmas lemmas
open import Data.Fin.Substitution.Unification application

{- Lemmas about unifiers -}
module _ where

  ≈≈-refl : ∀ {n} {t₁ : T₁ n} → t₁ ≈≈ t₁
  ≈≈-refl {t₁ = t₁} = unify id refl

  -- substitution preserves unifiability
  /-≈≈ : ∀ {n m} {t₁ t₂ : T₁ n} (ρ : Sub T₁ n m) → (t₁ / ρ) ≈≈ (t₂ / ρ) → t₁ ≈≈ t₂
  /-≈≈ ρ (unify φ eq) = unify (ρ ⊙ φ) (subst₂ _≡_ (sym (/-⊙ _)) (sym (/-⊙ _)) eq)

  /-≈/≈ : ∀ {n m} {t₁ t₂ : T₁ n} (ρ : Sub T₁ n m) → t₁ ≈/≈ t₂ → (t₁ / ρ) ≈/≈ (t₂ / ρ)
  /-≈/≈ ρ ¬u eq = ¬u (/-≈≈ ρ eq)

  -- variables are unifiable
  flex-flex : ∀ {m} → (x y : Fin m) → Unifier (var x) (var y)
  flex-flex {zero} ()
  flex-flex {suc m} x y with x Fin.≟ y
  ... | yes refl = unify id refl
  ... | no ¬eq   = unify (sub var (punchOut ¬eq) at x) (
    begin
      var x / (sub var (punchOut ¬eq) at x) ≡⟨ sub-at-x _ ⟩
      var (punchOut ¬eq)                    ≡⟨ sym (sub-at-not-x ¬eq) ⟩
      var y / (sub var (punchOut ¬eq) at x) ∎)
