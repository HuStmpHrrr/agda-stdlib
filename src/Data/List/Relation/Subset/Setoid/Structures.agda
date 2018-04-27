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
open import Relation.Binary.InducedStructures

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

≋-setoid : Setoid _ _
≋-setoid = InducedSetoid _⊆′_ ⊆′-refl ⊆′-trans

-- set equivalence relation
open Setoid ≋-setoid using () renaming (_≈_ to _≋_)

⊆′-preorder : Preorder _ _ _
⊆′-preorder = InducedPreorder _⊆′_ ⊆′-refl ⊆′-trans

⊆′-poset : Poset _ _ _
⊆′-poset = InducedPoset _⊆′_ ⊆′-refl ⊆′-trans

∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
∈-resp-≋ (xs⊆ys , _) x∈xs = ∈-resp-⊆′ xs⊆ys x∈xs

⊂-strictPartialOrder : StrictPartialOrder _ _ _
⊂-strictPartialOrder = InducedStrictPartialOrder _⊆′_ ⊆′-refl ⊆′-trans

open StrictPartialOrder ⊂-strictPartialOrder
     using ()
     renaming (_<_ to _⊂_)
