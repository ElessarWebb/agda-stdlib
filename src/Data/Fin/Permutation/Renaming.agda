open import Level hiding (lift; Lift)
open import Relation.Binary hiding (_⇒_)

module Data.Fin.Permutation.Renaming where

open import Function using (_∘_; _$_)
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Fin.Permutation
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec
open import Data.Vec.Properties

open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open P.≡-Reasoning

{- Permutable things -}
record Permute {ℓ₁}(T : ℕ → Set ℓ₁) : Set ℓ₁ where
  field
    permute : ∀ {m n} → Permutation m n → T m → T n

module UptoRenaming {ℓ₁ ℓ₂}
  (iset : IndexedSetoid ℕ ℓ₁ ℓ₂)
  (app : Permute (IndexedSetoid.Carrierᵢ iset)) where

  module TSet = IndexedSetoid iset
  open IndexedSetoid iset
    using ()
    renaming (
      Carrierᵢ to T
      ; _≈ᵢ_ to _T≈_)
  open Permute app

  record _≈_ {n} (t₁ t₂ : T n) : Set ℓ₂ where
    constructor ren
    field
      ρ   : Permutation n n
      prf : permute ρ t₁ T≈ t₂

  record PermuteLemmas : Set (ℓ₁ ⊔ ℓ₂) where
    field
      id-vanishes      : ∀ {n}(t : T n) → permute id t T≈ t
      permute-∘ₚ       : ∀ {m n o}(t : T m)(ρ₁ : Permutation m n)(ρ₂ : Permutation n o) → 
                          permute ρ₂ (permute ρ₁ t) T≈ permute (ρ₁ ∘ₚ ρ₂) t
      inverse-vanishes : ∀ {m n} t (ρ : Permutation m n) → permute (flip ρ) (permute ρ t) T≈ t
      permute-cong      : ∀ {m n} {t₁ t₂} {ρ : Permutation m n} → t₁ T≈ t₂ → permute ρ t₁ T≈ permute ρ t₂

  {- A term equivalence relation based on renamability (of free variables!) -}
  module TermEquiv (lemmas : PermuteLemmas) where
    open PermuteLemmas lemmas

    open _≈_
    open IsIndexedEquivalence

    ≈-Equiv : IsIndexedEquivalence T _≈_
    reflᵢ ≈-Equiv {_} {t} = record { ρ = id ; prf = id-vanishes t }
    transᵢ ≈-Equiv (ren ρ₁ eq₁) (ren ρ₂ eq₂) =
      ren
        (ρ₁ ∘ₚ ρ₂)
        (TSet.transᵢ (TSet.transᵢ (TSet.symᵢ (permute-∘ₚ _ ρ₁ ρ₂)) (permute-cong eq₁)) eq₂)
    symᵢ ≈-Equiv (ren ρ eq) =
      ren
        (flip ρ)
        (TSet.transᵢ (permute-cong (TSet.symᵢ eq)) (inverse-vanishes _ ρ))

    open IndexedSetoid using (Carrierᵢ; _≈ᵢ_; isEquivalenceᵢ)
    isetoid : IndexedSetoid ℕ _ _
    Carrierᵢ isetoid = T
    _≈ᵢ_ isetoid = _≈_
    isEquivalenceᵢ isetoid = ≈-Equiv

    open IndexedSetoid isetoid using (setoid; refl; sym; trans) public

module Propositional {ℓᵢ} (T : ℕ → Set ℓᵢ) (app : Permute T) where
  open import Data.Fin.Substitution
  open import Data.Fin.Substitution.Lemmas

  open import Relation.Binary.Indexed.Homogeneous.Construct.Propositional
  open UptoRenaming (indexedSetoid T) app public

-- We prove generically that a well-behaved substitution 
-- yields well-behaved permutation application
module FromApp {ℓᵢ} {T₁ T₂ : ℕ → Set ℓᵢ} (app : AppLemmas T₁ T₂) where
  module App = AppLemmas app
  open App using (_/_; var; lemmas₄)
  module Lem₄ = Lemmas₄ lemmas₄
  open Lemmas₄ lemmas₄ using (_⊙_) renaming (_/_ to _⊘_)

  ⟦_⟧ : ∀ {n n'} → Permutation n n' → Sub T₂ n n'
  ⟦ ρ ⟧ = tabulate (var ∘ ρ ⟨$⟩ʳ_)

  permuteT : Permute T₁
  permuteT = record { permute = λ ρ t → t / ⟦ ρ ⟧ }

  open Propositional T₁ permuteT
  open PermuteLemmas

  ⟦∘⟧ : ∀ {n m k} (ρ₁ : Permutation n m) (ρ₂ : Permutation m k) → ⟦ ρ₁ ⟧ ⊙ ⟦ ρ₂ ⟧ ≡ ⟦ ρ₁ ∘ₚ ρ₂ ⟧
  ⟦∘⟧ ρ₁ ρ₂ = extensionality (λ i →
      begin
      lookup i (map (_⊘ ⟦ ρ₂ ⟧) ⟦ ρ₁ ⟧) ≡⟨ lookup-map i (_⊘ ⟦ ρ₂ ⟧) ⟦ ρ₁ ⟧ ⟩
      lookup i ⟦ ρ₁ ⟧ ⊘ ⟦ ρ₂ ⟧ ≡⟨ P.cong (_⊘ _) (lookup∘tabulate _ i) ⟩
      var (ρ₁ ⟨$⟩ʳ i) ⊘ ⟦ ρ₂ ⟧ ≡⟨ Lem₄.var-/ ⟩
      lookup (ρ₁ ⟨$⟩ʳ i) ⟦ ρ₂ ⟧ ≡⟨ lookup∘tabulate _ (ρ₁ ⟨$⟩ʳ i) ⟩
      var ((ρ₁ ∘ₚ ρ₂) ⟨$⟩ʳ i) ≡⟨ P.sym (lookup∘tabulate _ i) ⟩
      lookup i ⟦ ρ₁ ∘ₚ ρ₂ ⟧ ∎)

  lemmas : PermuteLemmas

  id-vanishes lemmas t =
    let
      ρ-eq = extensionality (λ i →
        P.trans (lookup∘tabulate var i) (P.sym (App.lookup-id i)))
    in P.trans (P.cong (t /_) ρ-eq) (App.id-vanishes t)

  permute-∘ₚ  lemmas t ρ₁ ρ₂ =
    P.trans (P.sym (App./-⊙ t)) (P.cong (t /_) (⟦∘⟧ ρ₁ ρ₂))

  inverse-vanishes  lemmas t ρ = begin
    t / ⟦ ρ ⟧ / ⟦ flip ρ ⟧ ≡⟨ permute-∘ₚ lemmas t ρ (flip ρ) ⟩
    t / tabulate (var ∘ (ρ ∘ₚ flip ρ) ⟨$⟩ʳ_)
      ≡⟨ P.cong (λ ρ → t / ρ) (tabulate-cong (λ x → P.cong var (inverseˡ ρ))) ⟩
    t / tabulate (var ∘ id ⟨$⟩ʳ_) ≡⟨ id-vanishes lemmas t ⟩
    t ∎

  permute-cong      lemmas P.refl = P.refl

  module Lemmas = PermuteLemmas lemmas
