------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the subset relation over lists and setoid equality.
------------------------------------------------------------------------

module Data.List.Relation.Subset.Setoid.Properties where

open import Level
open import Data.List
open import Data.List.Any using (Any; here; there)
open import Data.Product

open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.InducedPreorders

module _ {c ℓ} (S : Setoid c ℓ) where

  open import Data.List.Relation.Subset.Setoid S
  open import Data.List.Membership.Setoid S
  open Setoid S renaming (Carrier to A)
  
  ⊆′-growʳ : ∀ {x : A} {l l′} → l ⊆′ l′ → l ⊆′ x ∷ l′
  ⊆′-growʳ {x} {.[]}      emp                = emp
  ⊆′-growʳ {x} {.(h ∷ _)} (grow h h∈l l⊆′l′) = grow h (there h∈l) (⊆′-growʳ l⊆′l′)
  
  l⊆′x∷l : ∀ {x l} → l ⊆′ x ∷ l
  l⊆′x∷l {x} {l = []} = emp
  l⊆′x∷l {x} {y ∷ l}  = grow y (there (here refl)) (⊆′-growʳ l⊆′x∷l)
  
  ⊆′-refl : Reflexive _⊆′_
  ⊆′-refl {[]}     = emp
  ⊆′-refl {x ∷ x₁} = grow x (here refl) l⊆′x∷l
  
  ⊆′-trans : Transitive _⊆′_
  ⊆′-trans emp              y⊆z = emp
  ⊆′-trans (grow h h∈y x⊆y) y⊆z = grow h (∈-resp-⊆′ y⊆z h∈y) (⊆′-trans x⊆y y⊆z)

  ⊆′-preorder : Preorder _ _ _
  ⊆′-preorder = InducedPreorder₃ S _⊆′_ ⊆′-refl ⊆′-trans  

  -- set equivalence relation
  _≋_ : List A → List A → Set _
  _≋_ = eq
    where open Preorder ⊆′-preorder renaming (_≈_ to eq)

  ∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
  ∈-resp-≋ (xs⊆ys , _) x∈xs = ∈-resp-⊆′ xs⊆ys x∈xs

  open import Relation.Binary.Properties.Preorder ⊆′-preorder public  
  open import Relation.Binary.NonStrictToStrict

  InducedStrictPartialOrder : StrictPartialOrder _ _ _
  InducedStrictPartialOrder = record
    { isStrictPartialOrder = <-isStrictPartialOrder _≋_ _⊆′_ isPartialOrder }
    where open Poset InducedPoset
    
