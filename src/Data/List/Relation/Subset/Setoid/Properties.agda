------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the subset relation over lists and setoid equality.
------------------------------------------------------------------------

module Data.List.Relation.Subset.Setoid.Properties where

open import Level
open import Data.List
open import Data.List.Membership.Setoid.Properties
open import Data.List.Any using (Any; here; there)
open import Data.Product

open import Relation.Nullary using (¬_)
open import Relation.Binary

module _ {c ℓ} (S : Setoid c ℓ) where

  open import Data.List.Relation.Subset.Setoid S
  open import Data.List.Membership.Setoid S
  open Setoid S renaming (Carrier to A)

  _≋_ : List A → List A → Set _
  l₁ ≋ l₂ = l₁ ⊆′ l₂ × l₂ ⊆′ l₁

  ⊆′-growʳ : ∀ {x : A} {l l′} → l ⊆′ l′ → l ⊆′ x ∷ l′
  ⊆′-growʳ {x} {.[]}      emp                = emp
  ⊆′-growʳ {x} {.(h ∷ _)} (grow h h∈l l⊆′l′) = grow h (there h∈l) (⊆′-growʳ l⊆′l′)
  
  l⊆′x∷l : ∀ {x l} → l ⊆′ x ∷ l
  l⊆′x∷l {x} {l = []} = emp
  l⊆′x∷l {x} {y ∷ l}  = grow y (there (here refl)) (⊆′-growʳ l⊆′x∷l)
  
  ⊆′-refl : Reflexive _⊆′_
  ⊆′-refl {[]}     = emp
  ⊆′-refl {x ∷ x₁} = grow x (here refl) l⊆′x∷l
  
  ≋-⊆′-reflexive : _≋_ ⇒ _⊆′_
  ≋-⊆′-reflexive = proj₁
  
  ≋-refl : ∀ {l} → l ≋ l
  ≋-refl = ⊆′-refl , ⊆′-refl
  
  ⊆′-trans : Transitive _⊆′_
  ⊆′-trans emp              y⊆z = emp
  ⊆′-trans (grow h h∈y x⊆y) y⊆z = grow h (∈-resp-⊆′ y⊆z h∈y) (⊆′-trans x⊆y y⊆z)
  
  ≋-trans : Transitive _≋_
  ≋-trans (x⊆y , y⊆x) (y⊆z , z⊆y) = ⊆′-trans x⊆y y⊆z , ⊆′-trans z⊆y y⊆x
  
  ⊆′-isPreorder : IsPreorder _≋_ _⊆′_
  ⊆′-isPreorder = record
    { isEquivalence = record
      { refl  = ≋-refl
      ; sym   = swap
      ; trans = ≋-trans
      }
    ; reflexive     = proj₁
    ; trans         = ⊆′-trans
    }
  
  ⊆′-preorder : Preorder _ _ _
  ⊆′-preorder = record { isPreorder = ⊆′-isPreorder }
  
  open import Relation.Binary.Properties.Preorder ⊆′-preorder public  
  open import Relation.Binary.NonStrictToStrict

  InducedStrictPartialOrder : StrictPartialOrder _ _ _
  InducedStrictPartialOrder = record
    { isStrictPartialOrder = <-isStrictPartialOrder _≋_ _⊆′_ isPartialOrder }
    where open Poset InducedPoset
    
