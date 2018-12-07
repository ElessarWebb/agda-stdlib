module Data.Vec.Permutation {ℓ}{A : Set ℓ} where

open import Data.Vec
open import Data.Vec.Properties
open import Data.Fin
open import Data.Fin.Permutation using (_⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ) renaming (Permutation to Renaming)
open import Data.Fin.Permutation.Renaming

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

{- Permutations of Vectors via Renaming -}
module _ where
  permute : ∀ {m n} → Renaming n m → Vec A n → Vec A m
  permute f xs = tabulate λ i → lookup (f ⟨$⟩ˡ i) xs

  vecPermute : Permute (Vec A)
  vecPermute = record { permute = permute }

  open Propositional (Vec A) vecPermute

  Permutation : ∀ {n} → Rel (Vec A n) ℓ
  Permutation = _≈_
    
{- Properties -}
module _ {n m}(φ : Renaming n m) where

  permute-replicate : ∀ {a : A} → permute φ (replicate a) ≡ replicate a
  permute-replicate {a} = tabulate-cong λ i → lookup-replicate (φ ⟨$⟩ˡ i) a

  lookup-permute : ∀ (xs : Vec A n) i → lookup (φ ⟨$⟩ʳ i) (permute φ xs) ≡ lookup i xs
  lookup-permute xs i = begin
    lookup (φ ⟨$⟩ʳ i) (permute φ xs) ≡⟨ lookup∘tabulate (λ j → lookup (φ ⟨$⟩ˡ j) xs) _ ⟩
    lookup (φ ⟨$⟩ˡ (φ ⟨$⟩ʳ i)) xs    ≡⟨ cong (λ j → lookup j xs) (inverseˡ φ) ⟩
    lookup i xs ∎
