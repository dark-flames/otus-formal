{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Pi where

open import Otus.Utils
open import Otus.Syntax hiding (lsuc; _⊔_)
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER
open import Otus.Semantics.Completeness.Relation.Neutral

open import Agda.Primitive using (lsuc; _⊔_)

private
  variable
    l l₁ l₂ : Level
    D : Set l
    t₁ t₂ v₁ v₂ u₁ u₂ : Value
    R : Rel D l₁
    R₁ : Rel D l₂
    F : RelFamily D l₂

data ⟦Π⟧ (R : Rel Value l₁) (F : RelFamily Value l₂) : Rel Value (l₁ ⊔ lsuc l₂) where
  PERPi : (v₁ ~ v₂ ∈ R → F v₁ R₁ × App⟨ t₁ ∣ v₁ ⟩⇝ u₁ × App⟨ t₂ ∣ v₂ ⟩⇝ u₂ × u₁ ~ u₂ ∈ R₁ )
    → t₁ ~ t₂ ∈ ⟦Π⟧ R F