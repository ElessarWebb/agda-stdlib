------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.Vec.Relation.Binary.Equality.Setoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.Vec.Relation.Equality.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.Vec.Relation.Binary.Equality.Setoid S public
