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
    v v₁ v₂ v₃ : D
    R₁ : Rel D l₁
    R₂ : Rel D l₂


infix 6 _~_∈_ _~_∈ᵣ_

record PER {l₁} (D : Set l₁) (l : Level) : Set (l₁ ⊔ lsuc l) where
  field
    rel : Rel D l
    isPER : IsPartialEquivalence rel

open IsPartialEquivalence {{...}}

_~_∈ᵣ_ : (v₁ v₂ : D) → (R : Rel D l₁) → Set l₁
v₁ ~ v₂ ∈ᵣ R = R v₁ v₂

_~_∈_ : (v₁ v₂ : D) → (R : PER D l₁) → Set l₁
v₁ ~ v₂ ∈ R = PER.rel R v₁ v₂


~-sym : (R : PER D l₁) → v₁ ~ v₂ ∈ R → v₂ ~ v₁ ∈ R
~-sym R = IsPartialEquivalence.sym (PER.isPER R)

~-trans : (R : PER D l₁) → v₁ ~ v₂ ∈ R → v₂ ~ v₃ ∈ R → v₁ ~ v₃ ∈ R
~-trans R = IsPartialEquivalence.trans (PER.isPER R)

~-left : (R : PER D l₁) → v₁ ~ v₂ ∈ R → v₁ ~ v₁ ∈ R
~-left R r = ~-trans R r (~-sym R r)

~-right : (R : PER D l₁) → v₁ ~ v₂ ∈ R → v₂ ~ v₂ ∈ R
~-right R r = ~-trans R (~-sym R r) r

~-convₗ : (R : PER D l₁) → v₁ ≡ v₂ → v₂ ~ v₃ ∈ R → v₁ ~ v₃ ∈ R
~-convₗ R refl = id

~-convᵣ : (R : PER D l₁) → v₁ ~ v₂ ∈ R → v₂ ≡ v₃ → v₁ ~ v₃ ∈ R
~-convᵣ R r refl = r

_⇔ₚ_ : ∀ {D : Set l} → PER D l₁ → PER D l₂ → Set (l ⊔ l₁ ⊔ l₂)
R₁ ⇔ₚ R₂ = PER.rel R₁ ⇔ PER.rel R₂

record PERFamily {D : Set l} (R : PER D l₁) (l₂ : Level) : Set (l ⊔ l₁ ⊔ lsuc l₂) where
  field
    Fam : D → PER D l₂ → Set l₂
    transport : ∀ {R₁} → v₁ ~ v₂ ∈ R → Fam v₁ R₁ → Fam v₂ R₁
    totality : v ~ v ∈ R → Σ[ R₁ ∈ PER D l₂ ] Fam v R₁
    coherent : ∀ {R₁ R₂} → v₁ ~ v₂ ∈ R → Fam v₁ R₁ → Fam v₂ R₂ → R₁ ⇔ₚ R₂

    
