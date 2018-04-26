------------------------------------------------------------------------
-- The Agda standard library
--
-- The subset relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Subset.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level
open import Data.List
open import Data.List.Membership.Setoid S
open import Data.List.Membership.Setoid.Properties
open import Data.List.Any using (Any; here; there)
open import Data.Product

open import Relation.Nullary using (¬_)
open import Relation.Binary

open import Function using (_∘_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊈_ _⊆′_ _⊈′_

_⊆_ : List A → List A → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : List A → List A → Set _
xs ⊈ ys = ¬ xs ⊆ ys

data _⊆′_ : List A → List A → Set (c ⊔ ℓ) where
  emp  : ∀ {l} → [] ⊆′ l
  grow : ∀ h {t l} → (h∈l : h ∈ l) → (t⊆l : t ⊆′ l) → h ∷ t ⊆′ l

_⊈′_ : List A → List A → Set _
l₁ ⊈′ l₂ = ¬ (l₁ ⊆′ l₂)

∈-resp-⊆′ : ∀ {x} → (x ∈_) Respects _⊆′_
∈-resp-⊆′ emp ()
∈-resp-⊆′ (grow h h∈l l₁⊆l₂) (here x≈h)   = ∈-resp-≈ S (sym x≈h) h∈l
∈-resp-⊆′ (grow h h∈l l₁⊆l₂) (there x∈l₁) = ∈-resp-⊆′ l₁⊆l₂ x∈l₁

⊆′⇒⊆ : ∀ {l₁ l₂} → l₁ ⊆′ l₂ → l₁ ⊆ l₂
⊆′⇒⊆ l₁⊆′l₂ = ∈-resp-⊆′ l₁⊆′l₂

⊆⇒⊆′ : ∀ {l₁ l₂} → l₁ ⊆ l₂ → l₁ ⊆′ l₂
⊆⇒⊆′ {[]}     l₁⊆l₂ = emp
⊆⇒⊆′ {x ∷ l₁} l₁⊆l₂ = grow x (l₁⊆l₂ (here refl)) (⊆⇒⊆′ (l₁⊆l₂ ∘ there))
