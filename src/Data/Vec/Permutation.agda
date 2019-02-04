module Data.Vec.Permutation where

open import Data.Vec
open import Data.Vec.Properties
open import Data.Fin
open import Data.Fin.Permutation renaming (Permutation to Renaming)
open import Data.Fin.Permutation.Renaming

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

{- Permutations of Vectors via Renaming -}
module _ {ℓ}{A : Set ℓ} where
  permute : ∀ {m n} → Renaming n m → Vec A n → Vec A m
  permute f xs = tabulate λ i → lookup (f ⟨$⟩ˡ i) xs

  vecPermute : Permute (Vec A)
  vecPermute = record { permute = permute }

  open Propositional (Vec A) vecPermute

  Permutation : ∀ {n} → Rel (Vec A n) ℓ
  Permutation = _≈_

  module VecPermutationLemmas where
    open PermuteLemmas
    lemmas : PermuteLemmas
    id-vanishes lemmas xs = extensionality (lookup∘tabulate _)
    permute-∘ₚ lemmas xs ρ₁ ρ₂ = extensionality λ i → begin
      lookup i (permute ρ₂ (permute ρ₁ xs)) ≡⟨ lookup∘tabulate _ i ⟩
      lookup (ρ₂ ⟨$⟩ˡ i) (permute ρ₁ xs) ≡⟨ lookup∘tabulate _ (ρ₂ ⟨$⟩ˡ i) ⟩
      lookup (ρ₁ ⟨$⟩ˡ (ρ₂ ⟨$⟩ˡ i)) xs ≡⟨ sym (lookup∘tabulate _ i) ⟩
      lookup i (permute (ρ₁ ∘ₚ ρ₂) xs) ∎
    inverse-vanishes lemmas xs ρ = begin
      permute (flip ρ) (permute ρ xs)
        ≡⟨ permute-∘ₚ lemmas xs ρ (flip ρ) ⟩
      permute (ρ ∘ₚ flip ρ) xs
        ≡⟨ extensionality (λ i → trans (lookup∘tabulate _ i) (cong (λ i₁ → lookup i₁ _) (inverseˡ ρ))) ⟩
      xs ∎
    permute-cong lemmas refl = refl

    open PermuteLemmas lemmas public
    
{- Properties -}
module _ {a}{A : Set a}{n m}(φ : Renaming n m) where
  open VecPermutationLemmas public

  permute-map : ∀ {b} {B : Set b} {xs} (f : A → B) → permute φ (map f xs) ≡ map f (permute φ xs)
  permute-map {xs = xs} f = extensionality λ i → begin
    lookup i (tabulate λ i → lookup (φ ⟨$⟩ˡ i) (map f xs))   ≡⟨ lookup∘tabulate _ i ⟩
    lookup (φ ⟨$⟩ˡ i) (map f xs)                             ≡⟨ lookup-map (φ ⟨$⟩ˡ i) _ xs ⟩
    f (lookup (φ ⟨$⟩ˡ i) xs)                                 ≡⟨ sym (lookup∘tabulate _ i) ⟩
    lookup i (tabulate (λ i → f (lookup (φ ⟨$⟩ˡ i) xs)))     ≡⟨ cong (lookup i) (tabulate-∘ _ _) ⟩
    lookup i (map f (tabulate (λ i → lookup (φ ⟨$⟩ˡ i) xs))) ∎

  permute-replicate : ∀ {a : A} → permute φ (replicate a) ≡ replicate a
  permute-replicate {a} = tabulate-cong λ i → lookup-replicate (φ ⟨$⟩ˡ i) a

  lookup-permute : ∀ (xs : Vec A n) i → lookup (φ ⟨$⟩ʳ i) (permute φ xs) ≡ lookup i xs
  lookup-permute xs i = begin
    lookup (φ ⟨$⟩ʳ i) (permute φ xs) ≡⟨ lookup∘tabulate (λ j → lookup (φ ⟨$⟩ˡ j) xs) _ ⟩
    lookup (φ ⟨$⟩ˡ (φ ⟨$⟩ʳ i)) xs    ≡⟨ cong (λ j → lookup j xs) (inverseˡ φ) ⟩
    lookup i xs ∎

  []=-permute⁺ : ∀ {x : A} {i xs} → xs [ i ]= x → permute φ xs [ φ ⟨$⟩ʳ i ]= x
  []=-permute⁺ {x} {i} {xs} e = lookup⇒[]= _ _ (trans (lookup-permute _ _) ([]=⇒lookup e))
  
  []=-permute⁻ : ∀ {x : A} {i xs} → permute φ xs [ φ ⟨$⟩ʳ i ]= x → xs [ i ]= x
  []=-permute⁻ {x} {i} {xs} e = lookup⇒[]= _ _ (trans (sym (lookup-permute _ _)) ([]=⇒lookup e))
