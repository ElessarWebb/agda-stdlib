open import Level hiding (lift; Lift)
open import Relation.Binary hiding (_⇒_)

module Data.Fin.Permutation.Renaming where

open import Data.Nat
open import Data.Fin.Permutation renaming (Permutation to Renaming)
open import Data.List

open import Relation.Binary.PropositionalEquality

{- Permutable things -}
record Rename {ℓ₁}(T : ℕ → Set ℓ₁) : Set ℓ₁ where
  field
    rename : ∀ {m n} → Renaming m n → T m → T n

module TermRenaming {ℓ₁}(T : ℕ → Set ℓ₁)(TRen : Rename T) where
  open Rename TRen

  {- t₁ is a renaming of t₂; i.e. alpha-equivalence on closed terms -}
  record _≈α_ {n} (t₁ t₂ : T n) : Set ℓ₁ where
    constructor ren
    field
      ρ   : Renaming n n
      prf : rename ρ t₁ ≡ t₂

  record RenameLemmas  : Set ℓ₁ where
    field
      id-vanishes      : ∀ {n}(t : T n) → rename id t ≡ t
      permute-∘ₚ       : ∀ {m n o}(t : T m)(ρ₁ : Renaming m n)(ρ₂ : Renaming n o) → 
                         rename ρ₂ (rename ρ₁ t) ≡ rename (ρ₁ ∘ₚ ρ₂) t
      inverse-vanishes : ∀ {m n} t (ρ : Renaming m n) → rename (flip ρ) (rename ρ t) ≡ t

    open _≈α_

    ≈αEquiv : ∀ {n} → IsEquivalence (_≈α_ {n})
    IsEquivalence.refl ≈αEquiv {t} = record { ρ = id ; prf = id-vanishes t }
    IsEquivalence.trans ≈αEquiv (ren ρ₁ refl) (ren ρ₂ refl) =
      ren (ρ₁ ∘ₚ ρ₂) (sym (permute-∘ₚ _ ρ₁ ρ₂))
    IsEquivalence.sym ≈αEquiv (ren ρ refl) = ren (flip ρ) (inverse-vanishes _ ρ)

    α-setoid : ∀ {n} → Setoid _ _
    Setoid.Carrier (α-setoid {n}) = T n
    Setoid._≈_ α-setoid = _≈α_
    Setoid.isEquivalence α-setoid = ≈αEquiv
