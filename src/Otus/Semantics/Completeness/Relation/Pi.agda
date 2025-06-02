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
    t₁ t₂ t₃ v₁ v₂ u₁ u₂ : Value
    R : PER Value l₁
    F : PERFamily R l₂
    R₁ : PER D l₂



PERΠ :  ∀ {l₁ l₂} → (R : PER Value l₁) → PERFamily R l₂ → Rel Value (l₁ ⊔ lsuc l₂)
PERΠ {l₁} {l₂} R F t₁ t₂ = ∀ {v₁ v₂ : Value} → v₁ ~ v₂ ∈ R 
      → Σ[ R₁ ∈ PER Value l₂ ] Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ]
        PERFamily.Fam F v₁ R₁ ×
        App⟨ t₁ ∣ v₁ ⟩⇝ u₁ ×
        App⟨ t₂ ∣ v₂ ⟩⇝ u₂ ×
        u₁ ~ u₂ ∈ R₁

open IsPartialEquivalence {{...}}

instance
  perΠ : ∀ {R : PER Value l₁} {F : PERFamily R l₂} → IsPartialEquivalence (PERΠ R F)
  sym {{ perΠ {_} {_} {R} {F}  }} r = λ { d → (let
      d' = ~-sym R d
      CD , u₁ , u₂ , fam₁ , app₁ , app₂ , r₁ = r d'
      fam₂ = PERFamily.transport F d' fam₁
    in CD , u₂ , u₁ , fam₂ , app₂ , app₁ , (~-sym CD r₁)) } 
  trans {{ perΠ {_} {_} {R} {F} }} l r = λ { d → (let
      d' = ~-sym R d
      dₗ = ~-left R d
      CDₗ , uₗ₁ , uₗ₂ , famₗ₁ , appₗ₁ , appₗ₂ , uEqₗ = l dₗ
      CDᵣ , uᵣ₁ , uᵣ₂ , famᵣ₁ , appᵣ₁ , appᵣ₂ , uEqᵣ = r d
      uₗ₂≡uᵣ₁ = appCong refl refl appₗ₂ appᵣ₁ 
      _ , r⇒l = PERFamily.coherent F dₗ famₗ₁ famᵣ₁
      uEq = ~-trans CDₗ uEqₗ (~-convₗ CDₗ uₗ₂≡uᵣ₁ (r⇒l uEqᵣ))
    in CDₗ , uₗ₁ , uᵣ₂ , famₗ₁ , appₗ₁ , appᵣ₂ , uEq )} 

⟦Π⟧ : (R : PER Value l₁) → PERFamily R l₂ → PER Value (l₁ ⊔ lsuc l₂)
⟦Π⟧ {l₁} {l₂} R F = record {rel = PERΠ R F ; isPER = perΠ {l₁} {l₂} {R} {F}}

 

