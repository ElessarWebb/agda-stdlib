------------------------------------------------------------------------
-- The Agda standard library
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Predicate.Sublist where

open import Data.Vec using ([]; _∷_)
open import Data.Empty hiding (⊥)
open import Data.Product hiding (map)
open import Data.List.Base hiding (lookup; [_])
open import Data.List.Properties
open import Data.List.Any using (here; there; satisfied)
open import Data.List.Any.Properties using (here-injective; there-injective)
open import Data.List.Membership.Propositional as Mem
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Sublist.Propositional
open import Data.List.Relation.Sublist.Propositional.Properties as SP hiding (bag⁺)
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Maybe.All as MAll using (nothing; just)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Sum as Sum using (_⊎_; [_,_]; inj₁; inj₂)

open import Function
import Function.Bijection as Bij
open import Function.Equivalence as Equiv using (_⇔_ ; equivalence)
import Function.Injection as Inj

open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Nullary
import Relation.Nullary.Decidable as D
open import Relation.Unary as U using (Pred)

------------------------------------------------------------------------
-- A sublist

module _ {a} {A : Set a} where
  open import Relation.Unary.Indexed using (IPred)
  open import Relation.Binary.Indexed.Homogeneous using (IRel)

  record Sublist (xs : List A) : Set a where
    constructor sub
    field
      {reify} : List A
      le      : reify ⊆ xs

  open Sublist using (reify)

  keep! : ∀ {x l} → Sublist l → Sublist (x ∷ l)
  keep! (sub p) = sub (keep p)

  skip! : ∀ {x l} → Sublist l → Sublist (x ∷ l)
  skip! (sub p) = sub (skip p)

  pattern base? = sub base
  pattern skip? x = sub (skip x)
  pattern keep? x = sub (keep x)

  ⊤ : ∀ {l} → Sublist l
  ⊤     = sub ⊆-refl

  ⊥ : ∀ {l} → Sublist l
  ⊥ {l} = sub ([]⊆ l) 

  only : ∀ {l x} → x ∈ l → Sublist l
  only = sub ∘ from∈

  NonEmpty : ∀ {l} → Sublist l → Set a 
  NonEmpty (sub {ys} prf) = ∃ λ y → y ∈ ys

  Empty : ∀ {l} → Sublist l → Set a
  Empty (sub {xs} _) = xs ≡ []

  Every : ∀ {l} → Sublist l → Set a
  Every {l} (sub {xs} _) = xs ≡ l

  _∪_ : ∀ {l} → (xs ys : Sublist l) → Sublist l
  _∪_ base?     _         = sub ([]⊆ [])
  _∪_ (keep? p) (keep? q) = keep! (sub p ∪ sub q)
  _∪_ (keep? p) (skip? q) = keep! (sub p ∪ sub q)
  _∪_ (skip? p) (keep? q) = keep! (sub p ∪ sub q)
  _∪_ (skip? p) (skip? q) = skip! (sub p ∪ sub q)

  _∩_ : ∀ {l} → (xs ys : Sublist l) → Sublist l
  _∩_ base?     _         = sub ([]⊆ [])
  _∩_ (keep? p) (keep? q) = keep! (sub p ∩ sub q)
  _∩_ (keep? p) (skip? q) = skip! (sub p ∩ sub q)
  _∩_ (skip? p) (keep? q) = skip! (sub p ∩ sub q)
  _∩_ (skip? p) (skip? q) = skip! (sub p ∩ sub q)

  _◆_ : ∀ {l} → (xs ys : Sublist l) → Set a
  xs ◆ ys = Empty (xs ∩ ys)

  Lift : ∀ {p} → Pred (List A) p → IPred Sublist p
  Lift P (sub {xs} _) = P xs

  Lift₂ : ∀ {p} → Rel (List A) p → IRel Sublist p
  Lift₂ R (sub {xs} _) (sub {ys} _) = R xs ys

  _⊑_ : IRel Sublist _
  _⊑_ = Lift₂ _⊆_

  infixl 4 _∈ₛ_
  _∈ₛ_ : ∀ {l} x (xs : Sublist l) → Set a
  _∈ₛ_ x = Lift (x ∈_)

  ∪-comm : ∀ {l} (xs ys : Sublist l) → xs ∪ ys ≡ ys ∪ xs
  ∪-comm (sub base) (sub base) = refl
  ∪-comm (skip? le) (skip? le') = cong skip! (∪-comm (sub le) (sub le'))
  ∪-comm (skip? le) (keep? le') = cong keep! (∪-comm (sub le) (sub le'))
  ∪-comm (keep? le) (skip? le') = cong keep! (∪-comm (sub le) (sub le'))
  ∪-comm (keep? le) (keep? le') = cong keep! (∪-comm (sub le) (sub le'))

  ∩-comm : ∀ {l} (xs ys : Sublist l) → xs ∩ ys ≡ ys ∩ xs
  ∩-comm (sub base) (sub base) = refl
  ∩-comm (skip? le) (skip? le') = cong skip! (∩-comm (sub le) (sub le'))
  ∩-comm (skip? le) (keep? le') = cong skip! (∩-comm (sub le) (sub le'))
  ∩-comm (keep? le) (skip? le') = cong skip! (∩-comm (sub le) (sub le'))
  ∩-comm (keep? le) (keep? le') = cong keep! (∩-comm (sub le) (sub le'))

  p⊑p∪q : ∀ {l} (p : Sublist l) (q : Sublist l) → p ⊑ (p ∪ q)
  p⊑p∪q base?      base? = base
  p⊑p∪q (skip? le) (skip? le') = p⊑p∪q (sub le) (sub le')
  p⊑p∪q (skip? le) (keep? le') = skip (p⊑p∪q (sub le) (sub le'))
  p⊑p∪q (keep? le) (skip? le') = keep (p⊑p∪q (sub le) (sub le'))
  p⊑p∪q (keep? le) (keep? le') = keep (p⊑p∪q (sub le) (sub le'))

  q⊑p∪q : ∀ {l} (p q : Sublist l) → q ⊑ (p ∪ q)
  q⊑p∪q p q rewrite ∪-comm p q = p⊑p∪q q p

  x∈p∪q⁻ : ∀ {l x} (p q : Sublist l) → x ∈ₛ p ∪ q → x ∈ₛ p ⊎ x ∈ₛ q
  x∈p∪q⁻ base? base? ()
  x∈p∪q⁻ {x ∷ xs} (skip? p) (skip? q) prf = x∈p∪q⁻ (sub p) (sub q) prf
  x∈p∪q⁻ {x ∷ xs} (skip? _) (keep? _) (here px) = inj₂ (here px)
  x∈p∪q⁻ {x ∷ xs} (skip? p) (keep? q) (there prf) =
    Sum.map id there (x∈p∪q⁻ {xs} (sub p) (sub q) prf)
  x∈p∪q⁻ {x ∷ xs} (keep? le) (skip? le₁) (here px) = inj₁ (here px)
  x∈p∪q⁻ {x ∷ xs} (keep? le) (keep? le₁) (here px) = inj₁ (here px)
  x∈p∪q⁻ {x ∷ xs} (keep? p) (skip? q) (there prf) =
    Sum.map there id (x∈p∪q⁻ {xs} (sub p) (sub q) prf)
  x∈p∪q⁻ {x ∷ xs} (keep? p) (keep? q) (there prf) =
    Sum.map there there (x∈p∪q⁻ {xs} (sub p) (sub q) prf)

  x∈p∪q⁺ : ∀ {l x} (p q : Sublist l) → x ∈ₛ p ⊎ x ∈ₛ q → x ∈ₛ p ∪ q
  x∈p∪q⁺ base? base? (inj₁ ())
  x∈p∪q⁺ base? base? (inj₂ ())
  x∈p∪q⁺ (skip? p) (skip? q) i                  = x∈p∪q⁺ (sub p) (sub q) i
  x∈p∪q⁺ (skip? p) (keep? q) (inj₁ x)           = there (x∈p∪q⁺ (sub p) (sub q) (inj₁ x))
  x∈p∪q⁺ (skip? p) (keep? q) (inj₂ (here refl)) = here refl
  x∈p∪q⁺ (skip? p) (keep? q) (inj₂ (there y))   = there (x∈p∪q⁺ (sub p) (sub q) (inj₂ y))
  x∈p∪q⁺ (keep? p) (skip? q) (inj₁ (here refl)) = here refl
  x∈p∪q⁺ (keep? p) (skip? q) (inj₁ (there x))   = there (x∈p∪q⁺ (sub p) (sub q) (inj₁ x))
  x∈p∪q⁺ (keep? p) (skip? q) (inj₂ y)           = there (x∈p∪q⁺ (sub p) (sub q) (inj₂ y))
  x∈p∪q⁺ (keep? p) (keep? q) (inj₁ (here refl)) = here refl
  x∈p∪q⁺ (keep? p) (keep? q) (inj₁ (there y))   = there (x∈p∪q⁺ (sub p) (sub q) (inj₁ y))
  x∈p∪q⁺ (keep? p) (keep? q) (inj₂ (here refl)) = here refl
  x∈p∪q⁺ (keep? p) (keep? q) (inj₂ (there y))   = there (x∈p∪q⁺ (sub p) (sub q) (inj₂ y))

  ⊥-Empty : ∀ {l} → Empty (⊥ {l})
  ⊥-Empty {l} = refl

  ⊥-unique : ∀ {l}{xs : Sublist l} → Empty xs → xs ≡ ⊥
  ⊥-unique {xs = base?} p = refl
  ⊥-unique {xs = skip? le} p with ⊥-unique {xs = sub le} p
  ... | refl = refl
  ⊥-unique {xs = keep? le} ()

  ⊤-unique : ∀ {l}(σ : Sublist l) → Every σ → σ ≡ ⊤
  ⊤-unique (base? )                      refl = refl
  ⊤-unique (skip? xs) refl = ⊥-elim (∷-⊈ xs)
  ⊤-unique (keep? xs) p with ⊤-unique (sub xs) (∷-injectiveʳ p)
  ⊤-unique (keep? .(⊆-reflexive refl)) p | refl = refl

  x∈only : ∀ {l x y} (i : x ∈ l) → y ∈ₛ only i → x ≡ y
  x∈only i (here refl) = refl
  x∈only i (there ())

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where
  open ≡-Reasoning
 
  ⊆-map⁺ : ∀ {l} → Sublist l → Sublist (map f l)
  ⊆-map⁺ (sub prf) = sub (map⁺ f prf)

  map-only : ∀ {l x} → (p : x ∈ l) → ⊆-map⁺ (only p) ≡ only (∈-map⁺ f p)
  map-only p = cong sub (map-from∈ p f) 

module _ {a} {A : Set a} where

  open import Data.List.Relation.BagAndSetEquality

  bag⁺ : ∀ {xs ys : List A} → xs ∼[ bag ] ys → Sublist xs → Sublist ys
  bag⁺ f (sub le) = sub (proj₁ (proj₂ (SP.bag⁺ f le))) 
