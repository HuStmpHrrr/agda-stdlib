------------------------------------------------------------------------
-- The Agda standard library
--
-- The subset relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Subset.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level
open import Data.List
open import Data.List.Membership.Setoid S public
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)
open import Data.List.Any using (Any; here; there)
open import Data.List.All

open import Relation.Nullary using (¬_)

open import Function using (_∘_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊈_ _⊆′_ _⊈′_

_⊆_ : List A → List A → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : List A → List A → Set _
xs ⊈ ys = ¬ xs ⊆ ys

_⊆′_ : List A → List A → Set _
xs ⊆′ ys = All (_∈ ys) xs

_⊈′_ : List A → List A → Set _
l₁ ⊈′ l₂ = ¬ (l₁ ⊆′ l₂)

∈-resp-⊆′ : ∀ {x} → (x ∈_) Respects _⊆′_
∈-resp-⊆′ [] ()
∈-resp-⊆′ (h∈l₁ ∷ l₁⊆l₂) (here x≈h)   = ∈-resp-≈ S (sym x≈h) h∈l₁
∈-resp-⊆′ (h∈l₁ ∷ l₁⊆l₂) (there x∈l₁) = ∈-resp-⊆′ l₁⊆l₂ x∈l₁

⊆′⇒⊆ : ∀ {l₁ l₂} → l₁ ⊆′ l₂ → l₁ ⊆ l₂
⊆′⇒⊆ l₁⊆′l₂ = ∈-resp-⊆′ l₁⊆′l₂

⊆⇒⊆′ : ∀ {l₁ l₂} → l₁ ⊆ l₂ → l₁ ⊆′ l₂
⊆⇒⊆′ {[]}     l₁⊆l₂ = []
⊆⇒⊆′ {x ∷ l₁} l₁⊆l₂ = l₁⊆l₂ (here refl) ∷ ⊆⇒⊆′ (l₁⊆l₂ ∘ there)
