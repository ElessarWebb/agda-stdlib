------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Relation.Sublist.Propositional.Properties where

open import Data.Vec using ([]; _∷_)
open import Data.Empty hiding (⊥)
open import Data.Product hiding (map)
open import Data.List.Base hiding (lookup)
open import Data.List.Properties
open import Data.List.Any using (here; there; satisfied)
open import Data.List.Any.Properties using (here-injective; there-injective)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Sublist.Propositional
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Maybe.All as MAll using (nothing; just)
open import Data.Nat.Base
open import Data.Nat.Properties

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
-- The `loookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {a} {A : Set a} where

  lookup-injective : ∀ {x : A} {xs ys} {p : xs ⊆ ys} {v w : x ∈ xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = skip p} {v} {w} eq =
    lookup-injective (there-injective eq)
  lookup-injective {p = keep p} {here px} {here qx} refl = refl
  lookup-injective {p = keep p} {there v} {there w} eq =
    cong there (lookup-injective (there-injective eq))
  -- impossible cases
  lookup-injective {p = keep p} {here px} {there w} ()
  lookup-injective {p = keep p} {there v} {here qx} ()
  lookup-injective {p = base} {}

  []∈-irrelevant : U.Irrelevant {A = List A} ([] ⊆_)
  []∈-irrelevant base     base     = refl
  []∈-irrelevant (skip p) (skip q) = cong skip ([]∈-irrelevant p q)

  [x]⊆xs↔x∈xs : ∀ {x : A} {xs} → ([ x ] ⊆ xs) Bij.⤖ (x ∈ xs)
  [x]⊆xs↔x∈xs {x} =
    Bij.bijection to∈ from∈ (to∈-injective _ _ refl) to∈∘from∈≗id

    where

    to∈-injective :
      ∀ {xs x y} (p : [ x ] ⊆ xs) (q : [ y ] ⊆ xs) (eq : x ≡ y) →
      to∈ p ≡ lookup q (here eq) →
      subst ((_⊆ xs) ∘ [_]) eq p ≡ q
    to∈-injective (skip p) (skip q) refl eq =
      cong skip (to∈-injective p q refl (there-injective eq))
    to∈-injective (keep p) (keep q) eq refl =
      cong keep ([]∈-irrelevant p q)
    to∈-injective (skip p) (keep q) refl ()
    to∈-injective (keep p) (skip q) refl ()

    to∈∘from∈≗id : ∀ {xs} (p : x ∈ xs) → to∈ (from∈ p) ≡ p
    to∈∘from∈≗id (here refl) = refl
    to∈∘from∈≗id (there p)   = cong there (to∈∘from∈≗id p)

------------------------------------------------------------------------
-- Some properties

module _ {a} {A : Set a} where

  ⊆-length : ∀ {xs ys : List A} → xs ⊆ ys → length xs ≤ length ys
  ⊆-length base     = ≤-refl
  ⊆-length (skip p) = ≤-step (⊆-length p)
  ⊆-length (keep p) = s≤s (⊆-length p)

------------------------------------------------------------------------
-- Relational properties

module _ {a} {A : Set a} where

  ⊆-reflexive : _≡_ ⇒ _⊆_ {A = A}
  ⊆-reflexive {[]}     refl = base
  ⊆-reflexive {x ∷ xs} refl = keep (⊆-reflexive refl)

  ⊆-refl : Reflexive {A = List A} _⊆_
  ⊆-refl = ⊆-reflexive refl

  ⊆-trans : Transitive {A = List A} _⊆_
  ⊆-trans p        base     = p
  ⊆-trans p        (skip q) = skip (⊆-trans p q)
  ⊆-trans (skip p) (keep q) = skip (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

  open ≤-Reasoning

  ⊆-antisym : Antisymmetric {A = List A} _≡_ _⊆_
  ⊆-antisym = λ p q → ⊆-antisym′ p q refl
    where
    ⊆-antisym′ : ∀ {xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ≡ zs → xs ≡ ys
    -- Positive cases
    ⊆-antisym′ base     base     refl = refl
    ⊆-antisym′ (keep p) (keep q) eq   =
      cong (_ ∷_) (⊆-antisym′ p q (cong (drop 1) eq))
    -- Dismissing the impossible cases
    ⊆-antisym′ {x ∷ xs} {y ∷ ys} (skip p) (skip q) refl =
      ⊥-elim $ 1+n≰n $ begin
        length (y ∷ ys) ≤⟨ ⊆-length q ⟩
        length xs       ≤⟨ n≤1+n (length xs) ⟩
        length (x ∷ xs) ≤⟨ ⊆-length p ⟩
        length ys       ∎
    ⊆-antisym′ {x ∷ xs} {y ∷ ys} (skip p) (keep q) refl =
      ⊥-elim $ 1+n≰n $ begin
        length (x ∷ xs) ≤⟨ ⊆-length p ⟩
        length ys       ≤⟨ ⊆-length q ⟩
        length xs       ∎
    ⊆-antisym′ {x ∷ xs} {y ∷ ys} (keep p) (skip q) refl =
      ⊥-elim $ 1+n≰n $ begin
        length (y ∷ ys) ≤⟨ ⊆-length q ⟩
        length xs       ≤⟨ ⊆-length p ⟩
        length ys       ∎

  ⊆-minimum : Minimum (_⊆_ {A = A}) []
  ⊆-minimum = []⊆_

module _ {a} (A : Set a) where

  ⊆-isPreorder : IsPreorder _≡_ (_⊆_ {A = A})
  ⊆-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ⊆-reflexive
    ; trans         = ⊆-trans
    }

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record
    { isPreorder = ⊆-isPreorder
    }

  ⊆-isPartialOrder : IsPartialOrder _≡_ _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = ⊆-isPreorder
    ; antisym    = ⊆-antisym
    }

  ⊆-poset : Poset _ _ _
  ⊆-poset = record
    { isPartialOrder = ⊆-isPartialOrder
    }

import Relation.Binary.PartialOrderReasoning as PosetReasoning
module ⊆-Reasoning {a} {A : Set a}  where
  private module P = PosetReasoning (⊆-poset A)
  open P public
    renaming (_≤⟨_⟩_ to _⊆⟨_⟩_; _≈⟨⟩_ to _≡⟨⟩_)
    hiding (_≈⟨_⟩_)


------------------------------------------------------------------------
-- Various functions' outputs are sublists

module _ {a} {A : Set a} where

  tail-⊆ : (xs : List A) → MAll.All (_⊆ xs) (tail xs)
  tail-⊆ []       = nothing
  tail-⊆ (x ∷ xs) = just (skip ⊆-refl)

  take-⊆ : ∀ n (xs : List A) → take n xs ⊆ xs
  take-⊆ zero    xs       = []⊆ xs
  take-⊆ (suc n) []       = []⊆ []
  take-⊆ (suc n) (x ∷ xs) = keep (take-⊆ n xs)

  drop-⊆ : ∀ n (xs : List A) → drop n xs ⊆ xs
  drop-⊆ zero    xs       = ⊆-refl
  drop-⊆ (suc n) []       = []⊆ []
  drop-⊆ (suc n) (x ∷ xs) = skip (drop-⊆ n xs)

module _ {a p} {A : Set a} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ []       = []⊆ []
  takeWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = keep (takeWhile-⊆ xs)
  ... | no ¬p = []⊆ x ∷ xs

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ []       = []⊆ []
  dropWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = skip (dropWhile-⊆ xs)
  ... | no ¬p = ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ []       = []⊆ []
  filter-⊆ (x ∷ xs) with P? x
  ... | yes p = keep (filter-⊆ xs)
  ... | no ¬p = skip (filter-⊆ xs)

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_


------------------------------------------------------------------------
-- _∷_

module _ {a} {A : Set a} where

  ∷⁻ : ∀ {x y} {us vs : List A} → x ∷ us ⊆ y ∷ vs → us ⊆ vs
  ∷⁻ (skip p) = ⊆-trans (skip ⊆-refl) p
  ∷⁻ (keep p) = p

  ∷-⊈ : ∀ {x : A} {xs} → ¬ (x ∷ xs ⊆ xs)
  ∷-⊈ p with ⊆-antisym p (skip (⊆-reflexive refl))
  ∷-⊈ p | ()

-- map

module _ {a b} {A : Set a} {B : Set b} where

  map⁺ : ∀ {xs ys} (f : A → B) → xs ⊆ ys → map f xs ⊆ map f ys
  map⁺ f base     = base
  map⁺ f (skip p) = skip (map⁺ f p)
  map⁺ f (keep p) = keep (map⁺ f p)

  open Inj.Injection

  map⁻ : ∀ {xs ys} (inj : A Inj.↣ B) →
         map (inj ⟨$⟩_) xs ⊆ map (inj ⟨$⟩_) ys → xs ⊆ ys
  map⁻ {[]}     {ys}     inj p = []⊆ ys
  map⁻ {x ∷ xs} {[]}     inj ()
  map⁻ {x ∷ xs} {y ∷ ys} inj p
    with inj ⟨$⟩ x | inspect (inj ⟨$⟩_) x
       | inj ⟨$⟩ y | inspect (inj ⟨$⟩_) y
       | injective inj {x} {y}
  map⁻ {x ∷ xs} {y ∷ ys} inj (skip p)
    | fx | Eq.[ eq ] | fy | _ | _ = skip (map⁻ inj (coerce p))
    where coerce = subst (λ fx → fx ∷ _ ⊆ _) (sym eq)
  map⁻ {x ∷ xs} {y ∷ ys} inj (keep p)
    | fx | _      | fx | _ | eq
    rewrite eq refl = keep (map⁻ inj p)

-- _++_

module _ {a} {A : Set a} where

  ++⁺ : ∀ {xs ys us vs : List A} → xs ⊆ ys → us ⊆ vs → xs ++ us ⊆ ys ++ vs
  ++⁺ base     q = q
  ++⁺ (skip p) q = skip (++⁺ p q)
  ++⁺ (keep p) q = keep (++⁺ p q)

  ++⁻ : ∀ xs {us vs : List A} → xs ++ us ⊆ xs ++ vs → us ⊆ vs
  ++⁻ []       p = p
  ++⁻ (x ∷ xs) p = ++⁻ xs (∷⁻ p)

  skips : ∀ {xs ys} (zs : List A) → xs ⊆ ys → xs ⊆ zs ++ ys
  skips zs = ++⁺ ([]⊆ zs)

-- take / drop

  ≤-take-⊆ : ∀ {m n} → m ≤ n → (xs : List A) → take m xs ⊆ take n xs
  ≤-take-⊆ z≤n     xs       = []⊆ take _ xs
  ≤-take-⊆ (s≤s p) []       = []⊆ []
  ≤-take-⊆ (s≤s p) (x ∷ xs) = keep (≤-take-⊆ p xs)

  ≥-drop-⊆ : ∀ {m n} → m ≥ n → (xs : List A) → drop m xs ⊆ drop n xs
  ≥-drop-⊆ {m} z≤n     xs       = drop-⊆ m xs
  ≥-drop-⊆     (s≤s p) []       = []⊆ []
  ≥-drop-⊆     (s≤s p) (x ∷ xs) = ≥-drop-⊆ p xs

  drop⁺ : ∀ n {xs ys : List A} → xs ⊆ ys → drop n xs ⊆ drop n ys
  drop⁺ zero    p        = p
  drop⁺ (suc n) base     = []⊆ []
  drop⁺ (suc n) (keep p) = drop⁺ n p
  drop⁺ (suc n) {xs} {y ∷ ys} (skip p) = begin
    drop (suc n) xs ⊆⟨ ≥-drop-⊆ (n≤1+n n) xs ⟩
    drop n xs       ⊆⟨ drop⁺ n p ⟩
    drop n ys       ∎ where open ⊆-Reasoning

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
         (P? : U.Decidable P) (Q? : U.Decidable Q) where

  ⊆-takeWhile-⊆ : (P U.⊆ Q) → ∀ xs → takeWhile P? xs ⊆ takeWhile Q? xs
  ⊆-takeWhile-⊆ P⊆Q []       = []⊆ []
  ⊆-takeWhile-⊆ P⊆Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = keep (⊆-takeWhile-⊆ P⊆Q xs)
  ... | yes px | no ¬qx = ⊥-elim $ ¬qx (P⊆Q px)
  ... | no ¬px | _      = []⊆ _

  ⊇-dropWhile-⊆ : (P U.⊇ Q) → ∀ xs → dropWhile P? xs ⊆ dropWhile Q? xs
  ⊇-dropWhile-⊆ P⊇Q []       = []⊆ []
  ⊇-dropWhile-⊆ P⊇Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = ⊇-dropWhile-⊆ P⊇Q xs
  ... | yes px | no ¬qx = skip (dropWhile-⊆ P? xs)
  ... | no ¬px | yes qx = ⊥-elim $ ¬px (P⊇Q qx)
  ... | no ¬px | no ¬qx = ⊆-refl

-- filter

  ⊆-filter-⊆ : (P U.⊆ Q) → ∀ xs → filter P? xs ⊆ filter Q? xs
  ⊆-filter-⊆ P⊆Q []       = []⊆ []
  ⊆-filter-⊆ P⊆Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = keep (⊆-filter-⊆ P⊆Q xs)
  ... | yes px | no ¬qx = ⊥-elim $ ¬qx (P⊆Q px)
  ... | no ¬px | yes qx = skip (⊆-filter-⊆ P⊆Q xs)
  ... | no ¬px | no ¬qx = ⊆-filter-⊆ P⊆Q xs

module _ {a p} {A : Set a} {P : Pred A p} (P? : U.Decidable P) where

  filter⁺ : ∀ {xs ys : List A} → xs ⊆ ys → filter P? xs ⊆ filter P? ys
  filter⁺                   base     = base
  filter⁺ {xs}     {y ∷ ys} (skip p) with P? y
  ... | yes py = skip (filter⁺ p)
  ... | no ¬py = filter⁺ p
  filter⁺ {x ∷ xs} {x ∷ ys} (keep p) with P? x
  ... | yes px = keep (filter⁺ p)
  ... | no ¬px = filter⁺ p

-- reverse

module _ {a} {A : Set a} where

  open ⊆-Reasoning

  reverse⁺ : {xs ys : List A} → xs ⊆ ys → reverse xs ⊆ reverse ys
  reverse⁺ base = []⊆ []
  reverse⁺ {xs} {y ∷ ys} (skip p) = begin
    reverse xs       ≡⟨ sym $ ++-identityʳ _ ⟩
    reverse xs ++ [] ⊆⟨ ++⁺ (reverse⁺ p) ([]⊆ _) ⟩
    reverse ys ∷ʳ y  ≡⟨ sym $ unfold-reverse y ys ⟩
    reverse (y ∷ ys) ∎
  reverse⁺ {x ∷ xs} {x ∷ ys} (keep p) = begin
    reverse (x ∷ xs) ≡⟨ unfold-reverse x xs ⟩
    reverse xs ∷ʳ x  ⊆⟨ ++⁺ (reverse⁺ p) ⊆-refl ⟩
    reverse ys ∷ʳ x  ≡⟨ sym $ unfold-reverse x ys ⟩
    reverse (x ∷ ys) ∎

  reverse⁻ : {xs ys : List A} → reverse xs ⊆ reverse ys → xs ⊆ ys
  reverse⁻ {xs} {ys} p = cast (reverse⁺ p) where
    cast = subst₂ _⊆_ (reverse-involutive xs) (reverse-involutive ys)


------------------------------------------------------------------------
-- Inversion lemmas

module _ {a} {A : Set a} where

  keep⁻¹ : ∀ (x : A) {xs ys} → (xs ⊆ ys) ⇔ (x ∷ xs ⊆ x ∷ ys)
  keep⁻¹ x = equivalence keep ∷⁻

  skip⁻¹ : ∀ {x y : A} {xs ys} → x ≢ y → (x ∷ xs ⊆ ys) ⇔ (x ∷ xs ⊆ y ∷ ys)
  skip⁻¹ ¬eq = equivalence skip $ λ where
    (skip p) → p
    (keep p) → ⊥-elim (¬eq refl)

  ++⁻¹ : ∀ (ps : List A) {xs ys} → (xs ⊆ ys) ⇔ (ps ++ xs ⊆ ps ++ ys)
  ++⁻¹ ps = equivalence (++⁺ ⊆-refl) (++⁻ ps)

------------------------------------------------------------------------
-- Decidability of the order

module Decidable
       {a} {A : Set a} (eq? : Decidable {A = A} _≡_) where

  infix 3 _⊆?_
  _⊆?_ : Decidable {A = List A} _⊆_
  []     ⊆? ys     = yes ([]⊆ ys)
  x ∷ xs ⊆? []     = no λ ()
  x ∷ xs ⊆? y ∷ ys with eq? x y
  ... | yes refl = D.map (keep⁻¹ x) (xs ⊆? ys)
  ... | no ¬eq   = D.map (skip⁻¹ ¬eq) (x ∷ xs ⊆? ys)

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

  q⊑p∪q : ∀ {l} {p : Sublist l} (q : Sublist l) → q ⊑ (p ∪ q)
  q⊑p∪q {p = p} q rewrite ∪-comm p q = p⊑p∪q q p

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

module _ {a b} {A : Set a} {B : Set b} where
 
  ⊆-map⁺ : ∀ {l}(f : A → B) → Sublist l → Sublist (map f l)
  ⊆-map⁺ f (sub prf) = sub (map⁺ f prf)

