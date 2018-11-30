------------------------------------------------------------------------
-- The Agda standard library
--
-- Using propositional equality on indexed sets yields an indexed setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation.Binary.Indexed.Homogeneous.Construct.Propositional
  {i} {I : Set i} where

open import Relation.Binary
open import Relation.Binary.Indexed.Homogeneous
  using (IsIndexedEquivalence; IndexedSetoid)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Structures

module _ {a} (A : I → Set a) where

  isIndexedEquivalence : IsIndexedEquivalence A _≡_
  isIndexedEquivalence = record
    { reflᵢ  = refl
    ; symᵢ   = sym
    ; transᵢ = trans
    }

  ------------------------------------------------------------------------
  -- Packages

  indexedSetoid : IndexedSetoid I a _
  indexedSetoid = record
    { isEquivalenceᵢ = isIndexedEquivalence }
