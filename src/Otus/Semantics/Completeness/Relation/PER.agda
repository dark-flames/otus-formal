{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.PER where

open import Otus.Utils
open import Otus.Syntax hiding (lsuc; _⊔_)
open import Otus.Semantics.Normal
open import Agda.Primitive using (lsuc; _⊔_)

private
  variable
    l l₁ l₂ : Level
    D : Set l
    v v₁ v₂ : D
    R₁ : Rel D l₁
    R₂ : Rel D l₂


infix 6 _~_∈_

_~_∈_ : (v₁ v₂ : D) → (R : Rel D l₁) → Set l₁
v₁ ~ v₂ ∈ R = R v₁ v₂

RelFamily : Set l₁ → (l : Level) → Set (lsuc l ⊔ l₁)
RelFamily D l = D → Rel D l → Set l

record IsRelFamily {D : Set l} (R : Rel D l₁) (F : RelFamily D l₂) : Set (l ⊔ l₁ ⊔ lsuc l₂) where
  field
    transport : ∀ {R₁} → v₁ ~ v₂ ∈ R → F v₁ R₁ → F v₂ R₁
    totality : v ~ v ∈ R → Σ[ R₁ ∈ Rel D l₂ ] F v R₁
    coherent : ∀ {R₁ R₂} → v₁ ~ v₂ ∈ R → F v₁ R₁ → F v₂ R₂ → R₁ ⇔ R₂

    
