------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the sublist relation over lists and propositional equality.
------------------------------------------------------------------------

module Data.List.Relation.Subset.Propositional.Properties where

open import Level using (Level)
open import Data.List
open import Data.Nat
open import Relation.Binary

open import Relation.Binary.PropositionalEquality using (setoid ; refl)
open import Data.List.Relation.Subset.Propositional
import Data.List.Relation.Subset.Propositional.Structures as SStructures

open import Function
open import Data.List.Any renaming (map to Amap)

open import Data.List.Membership.Setoid.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)

∈-concat⁺′ : ∀ {a} {A : Set a} {x : A} {l L} → x ∈ l → l ∈ L → x ∈ concat L
∈-concat⁺′ {A = A} x∈l (here refl) = ∈-++⁺ˡ (setoid A) x∈l
∈-concat⁺′ {A = A} x∈l (there {l′} l∈L) = ∈-++⁺ʳ (setoid A) l′ (∈-concat⁺′ x∈l l∈L)

module ∈⊆-Reasoning (a : Level) where

  import Relation.Binary.PartialOrderReasoning as PORe

  NList : ℕ → Set a → Set a
  NList zero    A = A
  NList (suc n) A = NList n (List A)

  -- |this is fairly tricky: we express the data type in GADT
  -- in order to learn about the hierarchy of types in containment
  -- reasoning.
  data _RelatesBy_To_ {A : Set a} : A → (n : ℕ) → NList n A → Set a where
    lvl0 : ∀ {x} → x RelatesBy 0 To x
    lvl+ : ∀ {x : A} {n l L} →
             (x∈l : x ∈ l) →
             (cont : l RelatesBy n To L) → x RelatesBy suc n To L

  private
    poset : Set a → Poset _ _ _
    poset A = struct.InducedPoset
      where module struct = SStructures A

    concats : ∀ {A} n → NList (suc n) A → List A
    concats zero    nl = nl
    concats (suc n) nl = concat (concats n nl)

    establish : ∀ {A : Set a} {x : A} {n L} →
                  x RelatesBy suc n To L → x ∈ concats n L
    establish {A} {n = zero}  (lvl+ x∈l lvl0) = x∈l
    establish {A} {n = suc n} (lvl+ x∈l lvl)  = ∈-concat⁺′ x∈l (establish lvl)

  -- Reasoning APIs go following

  module ⊆-Reasoning {A : Set a} where
    open PORe (poset A) renaming
         ( _≤⟨_⟩_ to _⊆⟨_⟩_
         ; begin_ to ⊆[_
         ; _∎ to _]
         )
         hiding (_≡⟨_⟩_) public

  open ⊆-Reasoning

  infix  3 _∎
  infixr 2 _∈⟨_⟩_ enlarge
  infix  1 begin_

  begin_ : ∀ {A : Set a} {x : A} {n L} →
             x RelatesBy suc n To L → x ∈ concats n L
  begin_ = establish

  _∈⟨_⟩_ : ∀ {A : Set a} (x : A) {l n L} →
             x ∈ l →
             l RelatesBy n To L → x RelatesBy suc n To L
  x ∈⟨ x∈l ⟩ ev = lvl+ x∈l ev

  syntax enlarge x l x∈l l⊆l′ ev = x ∈⟨ x∈l ⟩- l ⊆⟨ l⊆l′ ⟩ ev

  enlarge : ∀ {A : Set a} (x : A) l {l′ n L} (x∈l : x ∈ l) →
              l ⊆ l′ →
              l′ RelatesBy n To L → x RelatesBy suc n To L
  enlarge x l x∈l l⊆l′ ev = lvl+ (∈-resp-⊆ l⊆l′ x∈l) ev

  _∎ : ∀ {A : Set a} (x : A) → x RelatesBy 0 To x
  _∎ x = lvl0

  -- Following are examples

  private
    reasoning-example₁ : ∀ {A : Set a} (x : A) {l l′} → x ∈ l  → l ⊆ l′ → x ∈ l′
    reasoning-example₁ x {l} {l′} x≺l l≲l′ = begin
      x  ∈⟨ x≺l ⟩-
      l  ⊆⟨ l≲l′ ⟩
      l′ ∎

    reasoning-example₂ : ∀ {A : Set a} (x : A) {l l′ L} →
                           x ∈ l  → l ⊆ l′ → l′ ∈ L → x ∈ concat L
    reasoning-example₂ x {l} {l′} {L} x∈l l⊆l′ l′∈L = begin
      x  ∈⟨ x∈l ⟩-
      l  ⊆⟨ l⊆l′ ⟩
      l′ ∈⟨ l′∈L ⟩
      L  ∎

    reasoning-example₃ : ∀ {A : Set a} (x : A) {l l′ L Ł} →
                           x ∈ l →
                           l ∈ l′ → l′ ⊆ L →
                           L ∈ Ł →
                           x ∈ concat (concat Ł)
    reasoning-example₃ x {l} {l′} {L} {Ł} x∈l l∈l′ l′⊆L L∈Ł = begin
      x  ∈⟨ x∈l ⟩
      l  ∈⟨ l∈l′ ⟩-
      l′ ⊆⟨ ⊆[ l′ ⊆⟨ l′⊆L ⟩ L ] ⟩
      L  ∈⟨ L∈Ł ⟩
      Ł ∎
