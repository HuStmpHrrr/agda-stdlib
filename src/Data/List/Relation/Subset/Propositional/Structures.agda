------------------------------------------------------------------------
-- The Agda standard library
--
-- Induced strctures of the subset relation over lists and propositional equality.
------------------------------------------------------------------------


module Data.List.Relation.Subset.Propositional.Structures {a} (A : Set a) where

import Data.List.Relation.Subset.Setoid.Structures as SStructures
open import Relation.Binary.PropositionalEquality using (setoid)

open SStructures (setoid A) public
