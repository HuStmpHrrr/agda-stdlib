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


module Hierarchy {c ℓ} (S : Setoid c ℓ) where

  open import Data.Nat using (ℕ ; zero ; suc ; _+_)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

  Base : Setoid c ℓ
  Base = S

  module B = Lift S

  open Setoid Base using (Carrier)

  -- setoids that are used to generate more subset relations
  Subsetoids : ℕ → Setoid _ _
  Subsetoids zero    = B.≋-setoid
  Subsetoids (suc n) = L.≋-setoid
    where module L   = Lift (Subsetoids n)

  -- we here build a hierarchy of subset relations out of those subsetoids
  module Sub (n : ℕ) = Lift (Subsetoids n)

  Subcarriers : ℕ → Set _
  Subcarriers n = Setoid.Carrier (Subsetoids n)

  NList : ∀ {a} → ℕ → Set a → Set a
  NList zero    A = A
  NList (suc n) A = NList n (List A)

  concats′ : ∀ {a} {A : Set a} n → NList (suc n) A → List A
  concats′ zero    nl = nl
  concats′ (suc n) nl = concat (concats′ n nl)

  GNL : ℕ → ℕ → Set c
  GNL m n = NList m (NList n (List Carrier))

  NL : ℕ → Set c
  NL = GNL 0

  concats : ∀ n → NL n → NL 0
  concats = concats′

  NList-comm : ∀ {a} (A : Set a) → (n : ℕ) → NList n (List A) ≡ List (NList n A)
  NList-comm _ zero    = refl
  NList-comm _ (suc n) = NList-comm _ n

  gconcats : ∀ m n → GNL m n → NL n
  gconcats m n rewrite NList-comm Carrier n = concats′ m

  gconcats0⇒id : ∀ n → (l : NL n) → gconcats 0 n l ≡ l
  gconcats0⇒id zero l = refl
  gconcats0⇒id (suc n) l
    rewrite NList-comm (List Carrier) n = refl

  NL⇒GNL : ∀ m n → NL (m + n) ≡ GNL m n
  NL⇒GNL zero _        = refl
  NL⇒GNL (suc m) n
    rewrite NList-comm (List Carrier) (m + n)
          | NL⇒GNL m n = sym (NList-comm _ m)

  NL⇒GNL′ : ∀ m n → NL (suc m + n) ≡ GNL m (suc n)
  NL⇒GNL′ zero n    = refl
  NL⇒GNL′ (suc m) n
    rewrite NList-comm (List (List Carrier)) (m + n)
          | NL⇒GNL′ m n = sym (NList-comm _ m)

  subsetoid-carriers : ∀ n → Subcarriers n ≡ NL n
  subsetoid-carriers zero        = refl
  subsetoid-carriers (suc n)
    rewrite NList-comm (List Carrier) n
          | subsetoid-carriers n = refl

  contain-at′ : ∀ n (x : Subcarriers n) (xs : Subcarriers (suc n)) → Set (c ⊔ ℓ)
  contain-at′ n = _∈_
    where open Sub n

  subset-at′ : ∀ n (l₁ l₂ : Subcarriers (suc n)) → Set (c ⊔ ℓ)
  subset-at′ n = _⊆′_
    where open Sub n

  subset-at′-resp-contain-at′ : ∀ n {x} →
    (contain-at′ n x) Respects (subset-at′ n)
  subset-at′-resp-contain-at′ n = ∈-resp-⊆′
    where open Sub n

  -- following we will build a general membership and subset relation that is indexed
  -- by the setoid level given above
  infix 4 contain-at subset-at

  contain-at : ∀ n (x : NL n) (xs : NL (suc n)) → Set (c ⊔ ℓ)
  contain-at n
    rewrite sym (subsetoid-carriers (suc n))
          | sym (subsetoid-carriers n) = contain-at′ n
    where open Sub n
  syntax contain-at n x xs = x ∈[ n ] xs

  subset-at : ∀ n (l₁ l₂ : NL (suc n)) → Set (c ⊔ ℓ)
  subset-at n rewrite sym (subsetoid-carriers (suc n)) = subset-at′ n
  syntax subset-at n l₁ l₂ = l₁ ⊆[ n ] l₂


  ⊆[]-resp-∈[] : ∀ n {x} →
    (λ l₁ → x ∈[ n ] l₁) Respects (λ l₁ l₂ → l₁ ⊆[ n ] l₂)
  ⊆[]-resp-∈[] n
    rewrite sym (subsetoid-carriers (suc n))
          | sym (subsetoid-carriers n) = subset-at′-resp-contain-at′ n



-- we then build a reasoning API out of the previous hierarchy
module ∈⊆-Reasoning {c ℓ} (S : Setoid c ℓ) where

  open import Data.Nat using (ℕ ; suc ; zero ; _+_)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)
  
  import Data.Nat.Properties as ℕₚ
  import Relation.Binary.PartialOrderReasoning as PORe

  open Hierarchy S

  conv-NL : ∀ {n} m → NL (suc m + n) → NL (m + suc n)
  conv-NL {n} m nl rewrite ℕₚ.+-suc m n = nl

  data [_]_Related[_]_ : (n : ℕ) → NL n → (m : ℕ) → NL (m + n) → Set (c ⊔ ℓ) where
    lvl0 : ∀ {n x} → [ n ] x Related[ 0 ] x
    lvl+ : ∀ {n l L m} {Ł : NL (suc m + n)} →
             (l∈[n]L : l ∈[ n ] L) →
             [ suc n ] L Related[ m ] (conv-NL m Ł) →
             [ n ] l Related[ suc m ] Ł

  _∎ : ∀ {n} x → [ n ] x Related[ 0 ] x
  _ ∎ = lvl0

  _∈⟨_⟩_ : ∀ {n} l {L m Ł} →
             (l∈[n]L : l ∈[ n ] L) →
             [ suc n ] L Related[ m ] (conv-NL m Ł) →
             [ n ] l Related[ suc m ] Ł
  l ∈⟨ l∈[n]L ⟩ ev = lvl+ l∈[n]L ev

  enlarge : ∀ {n} (x : NL n) l {l′ m L} (x∈[n]l : x ∈[ n ] l) →
              l ⊆[ n ] l′ →
              [ suc n ] l′ Related[ m ] (conv-NL m L) →
              [ n ] x Related[ suc m ] L
  enlarge {n} x l x∈l l⊆l′ ev = lvl+ (⊆[]-resp-∈[] n l⊆l′ x∈l) ev
  syntax enlarge x l x∈l l⊆l′ ev = x ∈⟨ x∈l ⟩- l ⊆⟨ l⊆l′ ⟩ ev

  conv-NL′ : ∀ m {n} → NL (suc m + n) → GNL m (suc n)
  conv-NL′ m {n} nl rewrite NL⇒GNL′ m n = nl

  establish′ : ∀ {n l m L} → [ n ] l Related[ suc m ] L →
                 l ∈[ n ] gconcats m (suc n) (conv-NL′ m L)
  establish′ {n} {l} {.0} {L} (lvl+ l∈[n]L lvl0)
    rewrite gconcats0⇒id (suc n) L = l∈[n]L
  establish′ {n} {l} {.(suc _)} {L} (lvl+ l∈[n]L ev@(lvl+ l∈[n]L₁ ev′)) = {!establish′ ev!}

  module _ where
    open Lift S

    establish : ∀ x {l m L} → x ∈ l →
                  [ 0 ] l Related[ suc m ] L → x ∈ concats (suc m) (conv-NL′ m L)
    establish x {m = m} {L} x∈l ev = ∈-concat⁺′ S x∈l (establish′ ev)

    begin_∈⟨_⟩_ : ∀ x {l m L} → x ∈ l →
                    [ 0 ] l Related[ suc m ] L → x ∈ concats (suc m) (conv-NL′ m L)
    begin_∈⟨_⟩_ = establish
