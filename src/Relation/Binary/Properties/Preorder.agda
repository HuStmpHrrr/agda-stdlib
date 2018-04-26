------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by preorders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.Preorder
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Function
open import Data.Product as Prod

open Relation.Binary.Preorder P

-- The inverse relation is also a preorder.

invIsPreorder : IsPreorder _≈_ (flip _∼_)
invIsPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = reflexive ∘ Eq.sym
  ; trans         = flip trans
  }

invPreorder : Preorder p₁ p₂ p₃
invPreorder = record { isPreorder = invIsPreorder }

------------------------------------------------------------------------
-- For every preorder there is an induced equivalence

InducedEquivalence : Setoid _ _
InducedEquivalence = record
  { _≈_           = λ x y → x ∼ y × y ∼ x
  ; isEquivalence = record
    { refl  = (refl , refl)
    ; sym   = swap
    ; trans = Prod.zip trans (flip trans)
    }
  }

------------------------------------------------------------------------
-- For every preorder there is an induced poset over InducedEquivalence

InducedPoset : Poset _ _ _
InducedPoset = record
  { _≈_            = _≋_
  ; _≤_            = _∼_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = equiv
      ; reflexive     = proj₁
      ; trans         = trans
      }
    ; antisym    = _,_
    }
  } where open Setoid InducedEquivalence using ()
               renaming (_≈_ to _≋_ ; isEquivalence to equiv)
