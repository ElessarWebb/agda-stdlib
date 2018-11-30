module Data.Vec.Permutation where

open import Data.Vec
open import Data.Fin
open import Data.Fin.Permutation using (_⟨$⟩ˡ_) renaming (Permutation to Reordering)
open import Data.Fin.Permutation.Renaming

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module _ {ℓ}{A : Set ℓ} where
  permute : ∀ {m n} → Reordering n m → Vec A n → Vec A m
  permute f xs = tabulate λ i → lookup (f ⟨$⟩ˡ i) xs

  vecRename : Rename (Vec A)
  vecRename = record { rename = permute }

  open Propositional
  open RenameEquivalence (Vec A) vecRename

  Permutation : ∀ {n} → Rel (Vec A n) ℓ
  Permutation = _≈_
    
