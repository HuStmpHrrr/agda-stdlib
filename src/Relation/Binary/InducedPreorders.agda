------------------------------------------------------------------------
-- The Agda standard library
--
-- Induced preorders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.InducedPreorders
         {s₁ s₂}
         (S : Setoid s₁ s₂)  -- The underlying equality.
         where

open import Function
open import Data.Product

open Setoid S

-- Every respectful unary relation induces a preorder. (No claim is
-- made that this preorder is unique.)

InducedPreorder₁ : ∀ {p} (P : Carrier → Set p) →
                   P Respects _≈_ → Preorder _ _ _
InducedPreorder₁ P resp = record
  { _≈_        = _≈_
  ; _∼_        = λ c₁ c₂ → P c₁ → P c₂
  ; isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = resp
    ; trans         = flip _∘′_
    }
  }

-- Every respectful binary relation induces a preorder. (No claim is
-- made that this preorder is unique.)

InducedPreorder₂ : ∀ {a r} {A : Set a} →
                   (_R_ : A → Carrier → Set r) →
                   (∀ {x} → _R_ x Respects _≈_) → Preorder _ _ _
InducedPreorder₂ _R_ resp = record
  { _≈_        = _≈_
  ; _∼_        = λ c₁ c₂ → ∀ {a} → a R c₁ → a R c₂
  ; isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = λ c₁≈c₂ → resp c₁≈c₂
    ; trans         = λ c₁∼c₂ c₂∼c₃ → c₂∼c₃ ∘ c₁∼c₂
    }
  }

-- Every reflexive and transitive binary relation induces a preorder.

InducedPreorder₃ : ∀ {a r} {A : Set a} →
                     (_R_ : A → A → Set r) →
                     Reflexive _R_ → Transitive _R_ → Preorder _ _ _
InducedPreorder₃ _R_ refl trans = record
  { _≈_        = λ x y → x R y × y R x
  ; _∼_        = _R_
  ; isPreorder = record
    { isEquivalence = record
      { refl  = refl , refl
      ; sym   = swap
      ; trans = λ { (xRy , yRx) (yRz , zRy) → trans xRy yRz , trans zRy yRx }
      }
    ; reflexive     = proj₁
    ; trans         = trans
    }
  }
