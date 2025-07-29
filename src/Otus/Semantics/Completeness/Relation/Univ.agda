{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Univ where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER
open import Otus.Semantics.Completeness.Relation.Neutral
open import Otus.Semantics.Completeness.Relation.Nat
open import Otus.Semantics.Completeness.Relation.Pi

private
  variable
    l l₁ l₂ : Universe
    T T₁ T₂ t u v : Value
    E₁ E₂ : Closure
    n m : Neutral

data ⟦_⟧∷_≡_ : Value → Universe → PER Value 0ℓ → Set₁

data PERUniv : Universe → Rel Value 0ℓ where
  PERUnivNe : n ~ n ∈ Ne → l₁ ≡ l₂
    → ↑ n ∷ VUniv l₁ ~ ↑ n ∷ VUniv l₂ ∈ᵣ PERUniv l
  -- PERUnivPi : T₁ ~ T₂ ∈ᵣ PERUniv l
  --  → VPi T₁ E₁ ~ VPi T₂ E₂
  PERUnivNat : VNat ~ VNat ∈ᵣ PERUniv lBottom
  PERUnivUniv : l₁ ≡ l₂ → VUniv l₁ ~ VUniv l₂ ∈ᵣ PERUniv (lsuc l₁)

open IsPartialEquivalence {{...}}

instance 
  perUniv : ∀ {l : Universe} → IsPartialEquivalence (PERUniv l)
  sym {{perUniv}} (PERUnivNe q refl) = PERUnivNe (~-sym Ne q) refl
  sym {{perUniv}} PERUnivNat  = PERUnivNat
  sym {{perUniv}} (PERUnivUniv refl) = PERUnivUniv refl

  trans {{perUniv}} (PERUnivNe p refl) (PERUnivNe q refl) = PERUnivNe (~-trans Ne p q) refl
  trans {{perUniv}} PERUnivNat PERUnivNat = PERUnivNat
  trans {{perUniv}} (PERUnivUniv eq₁) (PERUnivUniv eq₂) = PERUnivUniv (≡-trans eq₁ eq₂)

⟦Univ⟧ : Universe → PER Value 0ℓ
⟦Univ⟧ l = record { rel = PERUniv l ; isPER = perUniv }

data ⟦_⟧∷_≡ᵣ_ where
  -- PERINe : ⟦ ↑ n ∷ VUniv l ⟧∷ lsuc l ≡ Ne
  PERINat : ⟦ VNat ⟧∷ lBottom ≡ᵣ ⟦Nat⟧
  PERIUniv : ⟦ VUniv l ⟧∷ lsuc l ≡ᵣ ⟦Univ⟧ l


