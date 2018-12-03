module Data.Vec.Permutation {ℓ}{A : Set ℓ} where

open import Data.Vec
open import Data.Vec.Properties
open import Data.Fin
open import Data.Fin.Permutation using (_⟨$⟩ˡ_) renaming (Permutation to Renaming)
open import Data.Fin.Permutation.Renaming

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

{- Permutations of Vectors via Renaming -}
module _ where
  permute : ∀ {m n} → Renaming n m → Vec A n → Vec A m
  permute f xs = tabulate λ i → lookup (f ⟨$⟩ˡ i) xs

  vecRename : Rename (Vec A)
  vecRename = record { rename = permute }

  open Propositional (Vec A) vecRename

  Permutation : ∀ {n} → Rel (Vec A n) ℓ
  Permutation = _≈_
    
{- Properties -}
module _ where

  -- permuting a constant vector vanishes
  permute-replicate : ∀ {a : A}{n m}(φ : Renaming n m) → permute φ (replicate a) ≡ replicate a
  permute-replicate {a} φ = tabulate-cong λ i → lookup-replicate (φ ⟨$⟩ˡ i) a

