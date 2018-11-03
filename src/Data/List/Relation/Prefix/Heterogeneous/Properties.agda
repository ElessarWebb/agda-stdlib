------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous prefix relation
------------------------------------------------------------------------

module Data.List.Relation.Prefix.Heterogeneous.Properties where

open import Data.Empty
open import Data.List.Base as List hiding (map; uncons)
-- using (List; []; _∷_; _++_; filter; take)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Prefix.Heterogeneous
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (proj₁; proj₂; uncurry)
open import Function

open import Relation.Nullary using (yes; no; ¬_)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- First as a decidable partial order (once made homogeneous)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromPointwise : Pointwise R ⇒ Prefix R
  fromPointwise []       = []
  fromPointwise (r ∷ rs) = r ∷ fromPointwise rs

  toPointwise : ∀ {as bs} → length as ≡ length bs →
                Prefix R as bs → Pointwise R as bs
  toPointwise {bs = []} eq [] = []
  toPointwise {bs = _ ∷ _} () []
  toPointwise eq (r ∷ rs) = r ∷ toPointwise (suc-injective eq) rs

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Prefix R) (Prefix S) (Prefix T)
  trans rs⇒t []       ss       = []
  trans rs⇒t (r ∷ rs) (s ∷ ss) = rs⇒t r s ∷ trans rs⇒t rs ss

module _ {a b r s e} {A : Set a} {B : Set b}
         {R : REL A B r} {S : REL B A s} {E : REL A B e} where

  antisym : Antisym R S E → Antisym (Prefix R) (Prefix S) (Pointwise E)
  antisym rs⇒e []            []            = []
  antisym rs⇒e (a∼b ∷ as∼bs) (b∼a ∷ bs∼as) = rs⇒e a∼b b∼a ∷ antisym rs⇒e as∼bs bs∼as

------------------------------------------------------------------------
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Pointwise R as bs →
        Prefix R cs ds → Prefix R (as ++ cs) (bs ++ ds)
  ++⁺ []            cs⊆ds = cs⊆ds
  ++⁺ (a∼b ∷ as∼bs) cs⊆ds = a∼b ∷ (++⁺ as∼bs cs⊆ds)

  ++⁻ : ∀ {as bs cs ds} → Pointwise R as bs →
        Prefix R (as ++ cs) (bs ++ ds) → Prefix R cs ds
  ++⁻ []            cs⊆ds         = cs⊆ds
  ++⁻ (a∼b ∷ as∼bs) (_ ∷ acs⊆bds) = ++⁻ as∼bs acs⊆bds

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix (λ a b → R (f a) (g b)) as bs →
         Prefix R (List.map f as) (List.map g bs)
  map⁺ f g []       = []
  map⁺ f g (r ∷ rs) = r ∷ map⁺ f g rs

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix R (List.map f as) (List.map g bs) →
         Prefix (λ a b → R (f a) (g b)) as bs
  map⁻ {[]}     {bs}     f g rs       = []
  map⁻ {a ∷ as} {[]}     f g ()
  map⁻ {a ∷ as} {b ∷ bs} f g (r ∷ rs) = r ∷ map⁻ f g rs

------------------------------------------------------------------------
-- filter

module _ {a b r p q} {A : Set a} {B : Set b} {R : REL A B r}
         {P : Pred A p} {Q : Pred B q} (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → R a b → P a → Q b) (Q⇒P : ∀ {a b} → R a b → Q b → P a)
         where

  filter⁺ : ∀ {as bs} →
            Prefix R as bs → Prefix R (filter P? as) (filter Q? bs)
  filter⁺ [] = []
  filter⁺ {a ∷ as} {b ∷ bs} (r ∷ rs) with P? a | Q? b
  ... | yes pa | yes qb = r ∷ filter⁺ rs
  ... | yes pa | no ¬qb = ⊥-elim (¬qb (P⇒Q r pa))
  ... | no ¬pa | yes qb = ⊥-elim (¬pa (Q⇒P r qb))
  ... | no ¬pa | no ¬qb = filter⁺ rs

------------------------------------------------------------------------
-- take

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  take⁺ : ∀ {as bs} n → Prefix R as bs → Prefix R (take n as) (take n bs)
  take⁺ zero    rs       = []
  take⁺ (suc n) []       = []
  take⁺ (suc n) (r ∷ rs) = r ∷ take⁺ n rs

------------------------------------------------------------------------
-- drop

  drop⁺ : ∀ {as bs} n → Prefix R as bs → Prefix R (drop n as) (drop n bs)
  drop⁺ zero    rs       = rs
  drop⁺ (suc n) []       = []
  drop⁺ (suc n) (r ∷ rs) = drop⁺ n rs

  drop⁻ : ∀ {as bs} n → Pointwise R (take n as) (take n bs) →
          Prefix R (drop n as) (drop n bs) → Prefix R as bs
  drop⁻                 zero    hds       tls = tls
  drop⁻ {[]}            (suc n) hds       tls = []
  drop⁻ {_ ∷ _} {[]}    (suc n) ()        tls
  drop⁻ {_ ∷ _} {_ ∷ _} (suc n) (r ∷ hds) tls = r ∷ (drop⁻ n hds tls)

------------------------------------------------------------------------
-- Decidability

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  prefix? : Decidable R → Decidable (Prefix R)
  prefix? R? []       bs       = yes []
  prefix? R? (a ∷ as) []       = no (λ ())
  prefix? R? (a ∷ as) (b ∷ bs) = Dec.map′ (uncurry _∷_) uncons
                               $ R? a b ×-dec prefix? R? as bs
