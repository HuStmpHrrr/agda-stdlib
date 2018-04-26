------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the subset relation over lists and setoid equality.
------------------------------------------------------------------------

module Data.List.Relation.Subset.Setoid.Properties where

open import Level using (Level ; _⊔_ ; lift)
open import Data.List
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.All
open import Data.Product
open import Data.List.Membership.Setoid.Properties using (∈-concat⁺ ; ∈-concat⁻)

import Data.List.Relation.Subset.Setoid as SSetoid
import Data.List.Relation.Subset.Setoid.Structures as SStructures
import Data.List.Membership.Setoid as MSetoid

open import Relation.Binary
open import Function

module Lift {c ℓ} (S : Setoid c ℓ) where
  open SSetoid S public
  open SStructures S public

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S

  private
    module L0 = Lift S
    Lequiv = L0.InducedEquivalence
    module MS1 = MSetoid Lequiv
    module L1 = Lift Lequiv

  -- following proofs show that there is something really general here

  ∈-concat⁺′ : ∀ {x l L} → x L0.∈ l → l L1.∈ L → x L0.∈ concat L
  ∈-concat⁺′ x∈l = ∈-concat⁺ S ∘ Any.map (flip L0.∈-resp-≋ x∈l)

  ∈-concat⁻′ : ∀ {v} xss → v L0.∈ concat xss → ∃ λ xs → v L0.∈ xs × xs L1.∈ xss
  ∈-concat⁻′ xss v∈c[xss] with MS1.find (∈-concat⁻ S xss v∈c[xss])
  ... | xs , t , s = xs , s , t

  ∉-concat : ∀ {x l L} → x L0.∉ concat L → l L1.∈ L → x L0.∉ l
  ∉-concat x∉⋃L = (flip ∘ curry) (x∉⋃L ∘ uncurry ∈-concat⁺′)

