open import Level hiding (lift; Lift)
open import Relation.Binary hiding (_⇒_)

module Data.Fin.Permutation.Renaming where

open import Data.Nat hiding (_⊔_)
open import Data.Fin.Permutation renaming (Permutation to Renaming)
open import Data.List

open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

{- Permutable things -}
record Rename {ℓ₁}(T : ℕ → Set ℓ₁) : Set ℓ₁ where
  field
    rename : ∀ {m n} → Renaming m n → T m → T n


module RenamingSetoid {ℓ₁ ℓ₂} (iset : IndexedSetoid ℕ ℓ₁ ℓ₂) where
  module TSet = IndexedSetoid iset
  open IndexedSetoid iset
    using ()
    renaming (
      Carrierᵢ to T
      ; _≈ᵢ_ to _T≈_)

  module RenameEquivalence (app : Rename T) where
    open Rename app

    record _≈_ {n} (t₁ t₂ : T n) : Set ℓ₂ where
      constructor ren
      field
        ρ   : Renaming n n
        prf : rename ρ t₁ T≈ t₂

  record RenameLemmas : Set (ℓ₁ ⊔ ℓ₂) where
    field
      app : Rename T

    open Rename app public

    field
      id-vanishes      : ∀ {n}(t : T n) → rename id t T≈ t
      permute-∘ₚ       : ∀ {m n o}(t : T m)(ρ₁ : Renaming m n)(ρ₂ : Renaming n o) → 
                         rename ρ₂ (rename ρ₁ t) T≈ rename (ρ₁ ∘ₚ ρ₂) t
      inverse-vanishes : ∀ {m n} t (ρ : Renaming m n) → rename (flip ρ) (rename ρ t) T≈ t
      rename-cong      : ∀ {m n} {t₁ t₂} {ρ : Renaming m n} → t₁ T≈ t₂ → rename ρ t₁ T≈ rename ρ t₂

  {- A term equivalence relation based on renamability (of free variables!) -}
  record TermEquiv : Set (ℓ₁ ⊔ ℓ₂) where
    field
      lemmas   : RenameLemmas

    open RenameLemmas lemmas
    open RenameEquivalence app

    open _≈_
    open IsIndexedEquivalence
    
    ≈-Equiv : IsIndexedEquivalence T _≈_
    reflᵢ ≈-Equiv {_} {t} = record { ρ = id ; prf = id-vanishes t }
    transᵢ ≈-Equiv (ren ρ₁ eq₁) (ren ρ₂ eq₂) =
      ren
        (ρ₁ ∘ₚ ρ₂)
        (TSet.transᵢ (TSet.transᵢ (TSet.symᵢ (permute-∘ₚ _ ρ₁ ρ₂)) (rename-cong eq₁)) eq₂)
    symᵢ ≈-Equiv (ren ρ eq) =
      ren
        (flip ρ)
        (TSet.transᵢ (rename-cong (TSet.symᵢ eq)) (inverse-vanishes _ ρ))

    open IndexedSetoid using (Carrierᵢ; _≈ᵢ_; isEquivalenceᵢ)
    setoid : IndexedSetoid ℕ _ _
    Carrierᵢ setoid = T
    _≈ᵢ_ setoid = _≈_
    isEquivalenceᵢ setoid = ≈-Equiv

module Propositional {ℓᵢ} (T : ℕ → Set ℓᵢ) where
  open import Relation.Binary.Indexed.Homogeneous.Construct.Propositional
  open RenamingSetoid (indexedSetoid T) public
