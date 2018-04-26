------------------------------------------------------------------------
-- The Agda standard library
--
-- Induced strctures of the subset relation over lists and setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Subset.Setoid.Structures {c ℓ} (S : Setoid c ℓ) where

open import Level
open import Data.List
open import Data.List.Any using (Any; here; there)
open import Data.List.All
open import Data.Product

open import Relation.Nullary using (¬_)
open import Relation.Binary.InducedPreorders

open import Data.List.Relation.Subset.Setoid S
open Setoid S renaming (Carrier to A)

⊆′-growʳ : ∀ {x : A} {l l′} → l ⊆′ l′ → l ⊆′ x ∷ l′
⊆′-growʳ {x} {.[]}   []            = []
⊆′-growʳ {x} {_ ∷ _} (h∈l ∷ l⊆′l′) = there h∈l ∷ ⊆′-growʳ l⊆′l′

l⊆′x∷l : ∀ {x l} → l ⊆′ x ∷ l
l⊆′x∷l {x} {l = []} = []
l⊆′x∷l {x} {y ∷ l}  = there (here refl) ∷ ⊆′-growʳ l⊆′x∷l

⊆′-refl : Reflexive _⊆′_
⊆′-refl {[]}     = []
⊆′-refl {x ∷ x₁} = here refl ∷ l⊆′x∷l

⊆′-trans : Transitive _⊆′_
⊆′-trans []          y⊆z = []
⊆′-trans (h∈y ∷ x⊆y) y⊆z = ∈-resp-⊆′ y⊆z h∈y ∷ ⊆′-trans x⊆y y⊆z

⊆′-preorder : Preorder _ _ _
⊆′-preorder = InducedPreorder₃ S _⊆′_ ⊆′-refl ⊆′-trans

-- set equivalence relation
_≋_ : List A → List A → Set _
_≋_ = Preorder._≈_ ⊆′-preorder

∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
∈-resp-≋ (xs⊆ys , _) x∈xs = ∈-resp-⊆′ xs⊆ys x∈xs

open import Relation.Binary.Properties.Preorder ⊆′-preorder public
open import Relation.Binary.NonStrictToStrict

InducedStrictPartialOrder : StrictPartialOrder _ _ _
InducedStrictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder _≋_ _⊆′_ isPartialOrder }
  where open Poset InducedPoset
