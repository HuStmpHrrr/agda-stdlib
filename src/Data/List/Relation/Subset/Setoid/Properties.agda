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
    Lequiv = L0.≋-setoid
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


-- base setoid, then we spawn more setoids using this
module ∈⊆-Reasoning {c ℓ} (S : Setoid c ℓ) where

  open import Data.Nat using (ℕ ; zero ; suc ; _+_)
  import Relation.Binary.PartialOrderReasoning as PORe
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

  open Setoid S using (Carrier)

  private
    -- setoid level - 1, setoids spawned off base setoid
    subsetoids : ℕ → Setoid _ _
    subsetoids zero    = L.≋-setoid
      where module L   = Lift S
    subsetoids (suc n) = L.≋-setoid
      where module L   = Lift (subsetoids n)

  Subcarriers : ℕ → Set _
  Subcarriers n = Setoid.Carrier (subsetoids n)

  NList : ∀ {a} → ℕ → Set a → Set a
  NList zero    A = A
  NList (suc n) A = NList n (List A)

  concats′ : ∀ {a} {A : Set a} n → NList (suc n) A → List A
  concats′ zero    nl = nl
  concats′ (suc n) nl = concat (concats′ n nl)

  NL : ℕ → Set c
  NL n = NList n (List Carrier)

  concats : ∀ n → NL n → List Carrier
  concats n nl = concats′ n nl

  private
    NList-comm : ∀ {a} (A : Set a) → (n : ℕ) → NList n (List A) ≡ List (NList n A)
    NList-comm _ zero    = refl
    NList-comm _ (suc n) = NList-comm _ n

    subsetoid-carriers : ∀ n → Subcarriers n ≡ NL n
    subsetoid-carriers zero        = refl
    subsetoid-carriers (suc n)
      rewrite NList-comm (List Carrier) n
            | subsetoid-carriers n = refl

  contain-at′ : ∀ n (x : Subcarriers n) (xs : Subcarriers (suc n)) → Set (c ⊔ ℓ)
  contain-at′ n = _∈_
    where open Lift (subsetoids n)

  subset-at′ : ∀ n (l₁ l₂ : Subcarriers (suc n)) → Set (c ⊔ ℓ)
  subset-at′ n = _⊆′_
    where open Lift (subsetoids n)

  subset-at′-resp-contain-at′ : ∀ n {x} →
    (contain-at′ n x) Respects (subset-at′ n)
  subset-at′-resp-contain-at′ n = ∈-resp-⊆′
    where open Lift (subsetoids n)

  contain-at : ∀ n (x : NL n) (xs : NL (suc n)) → Set (c ⊔ ℓ)
  contain-at n
    rewrite sym (subsetoid-carriers (suc n))
          | sym (subsetoid-carriers n) = contain-at′ n
    where open Lift (subsetoids n)
  syntax contain-at n x xs = x ∈[ n ] xs

  subset-at : ∀ n (l₁ l₂ : NL (suc n)) → Set (c ⊔ ℓ)
  subset-at n
    rewrite sym (subsetoid-carriers (suc n)) = subset-at′ n
  syntax subset-at n l₁ l₂ = l₁ ⊆[ n ] l₂

  ⊆[]-resp-∈[] : ∀ n {x} →
    (λ l₁ → x ∈[ n ] l₁) Respects (λ l₁ l₂ → l₁ ⊆[ n ] l₂)
  ⊆[]-resp-∈[] n
    rewrite sym (subsetoid-carriers (suc n))
          | sym (subsetoid-carriers n) = subset-at′-resp-contain-at′ n

  data [_]_Related[_]_ : (n : ℕ) → NL n → (m : ℕ) → NL m → Set (c ⊔ ℓ) where
    lvl0 : ∀ {n x} → [ n ] x Related[ n ] x
    lvl+ : ∀ {n l L m} {Ł : NL m} →
             (l∈[n]L : l ∈[ n ] L) →
             [ suc n ] L Related[ m ] Ł →
             [ n ] l Related[ m ] Ł

  _∎ : ∀ {n} x → [ n ] x Related[ n ] x
  _ ∎ = lvl0

  _∈⟨_⟩_ : ∀ {n} l {L m} {Ł : NL m} →
             (l∈[n]L : l ∈[ n ] L) →
             [ suc n ] L Related[ m ] Ł →
             [ n ] l Related[ m ] Ł
  l ∈⟨ l∈[n]L ⟩ ev = lvl+ l∈[n]L ev

  enlarge : ∀ {n} (x : NL n) l {l′ m L} (x∈[n]l : x ∈[ n ] l) →
              l ⊆[ n ] l′ →
              [ suc n ] l′ Related[ m ] L →
              [ n ] x Related[ m ] L
  enlarge {n} x l x∈l l⊆l′ ev = lvl+ (⊆[]-resp-∈[] n l⊆l′ x∈l) ev
  syntax enlarge x l x∈l l⊆l′ ev = x ∈⟨ x∈l ⟩- l ⊆⟨ l⊆l′ ⟩ ev

  open import Relation.Nullary using (¬_)

  progressive-reasoning : ∀ {n m x y} → ¬ ([ suc n + m ] x Related[ m ] y)
  progressive-reasoning {n} {zero} (lvl+ l∈[n]L ev) = progressive-reasoning {suc n} ev
  progressive-reasoning {n} {suc m} ev = {!!}

  module _ where
    open Lift S

    -- establish : ∀ x {l m L} → x ∈ l → [ 0 ] l Related[ m ] L → x ∈ concats m L
    -- establish x {m = zero} x∈l lvl0 = x∈l
    -- establish x {m = zero} x∈l (lvl+ l∈[n]L ev) with progressive-reasoning ev
    -- ... | ()
    -- establish x {m = suc m} x∈l (lvl+ l∈[n]L ev) = {!∈-concat⁺′ S x∈l !}
