------------------------------------------------------------------------
-- The Agda standard library
--
-- The sublist relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Sublist.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Relation.Subset.Setoid as Subset

open Subset S using (_⊆_ ; _⊈_) public
