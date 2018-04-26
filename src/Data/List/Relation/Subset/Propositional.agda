------------------------------------------------------------------------
-- The Agda standard library
--
-- The subset relation over propositional equality.
------------------------------------------------------------------------

module Data.List.Relation.Subset.Propositional {a} {A : Set a} where

import Data.List.Relation.Subset.Setoid as SSetoid
open import Relation.Binary.PropositionalEquality using (setoid)
open import Data.List

open SSetoid (setoid A) using (_∈_ ; _∉_)
     renaming (_⊆′_ to _⊆_ ; _⊈′_ to _⊈_ ; ∈-resp-⊆′ to ∈-resp-⊆) public
