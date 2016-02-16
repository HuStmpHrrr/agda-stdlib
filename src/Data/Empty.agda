------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type
------------------------------------------------------------------------

module Data.Empty where

open import Level

data ⊥ : Set where

{-# HASKELL data AgdaEmpty #-}
{-# COMPILED_DATA ⊥ MAlonzo.Code.Data.Empty.AgdaEmpty #-}

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
