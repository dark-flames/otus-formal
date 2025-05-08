{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Term where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id; _∘_)

record ULevelConjInversion : Set where
  constructor uLvlConjInv
  field
    l l₁ l₂ : ULevel
    l₁⊔l₂≡l : l₁ ⊔ l₂ ≡ l

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Δ' Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B T : Term

piTmInversion : Γ ⊢ Pi A B ∷ T → Σ[ inv ∈ ULevelConjInversion ] 
    (Γ ⊢ T ≡ⱼ U (ULevelConjInversion.l inv)) × (Γ ⊢ A ∷ U (ULevelConjInversion.l₁ inv)) × (Γ , A ⊢ B ∷ U (ULevelConjInversion.l₂ inv))
piTmInversion (TmPi Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂) = let l₁ = univInversion Γ⊢A∷Ul₁
  in let l₂ = univInversion Γ,A⊢B∷Ul₂
  in let ⊢Γ = tmWfCtx Γ⊢A∷Ul₁
  in let inv = uLvlConjInv (l₁ ⊔ l₂) l₁ l₂ refl
  in pair inv (pair (TyEqRefl (TyU ⊢Γ)) (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂))
piTmInversion (TmTyConv Γ⊢PiAB∷G Γ⊢G≡T) = let pair inv (pair Γ⊢G≡Ul (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂)) = piTmInversion Γ⊢PiAB∷G
  in let Γ⊢T≡Ul = TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡Ul
  in pair inv (pair Γ⊢T≡Ul (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂))