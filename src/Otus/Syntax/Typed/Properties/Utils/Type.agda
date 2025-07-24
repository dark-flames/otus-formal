{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Utils.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presupposition

open PropositionalEq

private
  variable
    l₁ l₂ : ULevel
    x : ℕ
    Γ Δ Ξ Θ : Context
    γ γ₁ γ₂ δ ξ : Substitution
    A B C D : Term

tyEqPi₁ : Γ ⊢ A → Γ ⊢ A ≡ⱼ B → Γ ◁ A ⊢ C
    → Γ ⊢ Pi A C ≡ⱼ Pi B C
tyEqPi₁ Γ⊢A Γ⊢A≡B Γ◁A⊢C = TyEqPi Γ⊢A Γ⊢A≡B (TyEqRefl Γ◁A⊢C)

tyEqPi₂ : Γ ⊢ A → Γ ◁ A ⊢ C ≡ⱼ D
    → Γ ⊢ Pi A C ≡ⱼ Pi A D
tyEqPi₂ Γ⊢A Γ◁A⊢C≡D = TyEqPi Γ⊢A (TyEqRefl Γ⊢A) Γ◁A⊢C≡D

tyEqSubst₁ : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ A [ γ ]ₑ ≡ⱼ B [ γ ]ₑ
tyEqSubst₁ Δ⊢A≡B Γ⊢γ⇒Δ = TyEqSubst Δ⊢A≡B (SbEqRefl Γ⊢γ⇒Δ)

tyEqSubst₂ : Δ ⊢ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ A [ γ₂ ]ₑ
tyEqSubst₂ Δ⊢A Γ⊢γ₁≡γ₂⇒Δ = TyEqSubst (TyEqRefl Δ⊢A) Γ⊢γ₁≡γ₂⇒Δ

tyUnivCong : ⊢ Γ → l₁ ≡ l₂ → Γ ⊢ Univ l₁ ≡ⱼ Univ l₂
tyUnivCong ⊢Γ refl = TyEqRefl (TyUniv ⊢Γ)

tyEq3Sb : Θ ⊢ A → Ξ ⊢ ξ ⇒ Θ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ A [ ξ ]ₑ [ δ ]ₑ [ γ ]ₑ ≡ⱼ A [ ξ ∘ δ ∘ γ ]ₑ
tyEq3Sb Θ⊢A Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let
    Δ⊢A[ξ][δ]≡A[ξ∘δ] = TyEqSubstSubst Θ⊢A Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ
    Δ⊢ξ∘δ⇒Θ = SbComp Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ
    Γ⊢A[ξ][δ][γ]≡A[ξ∘δ][γ] = tyEqSubst₁ Δ⊢A[ξ][δ]≡A[ξ∘δ] Γ⊢γ⇒Δ
    Γ⊢A[ξ∘δ][γ]≡A[ξ∘δ∘γ] = TyEqSubstSubst Θ⊢A Δ⊢ξ∘δ⇒Θ Γ⊢γ⇒Δ
  in TyEqTrans Γ⊢A[ξ][δ][γ]≡A[ξ∘δ][γ] Γ⊢A[ξ∘δ][γ]≡A[ξ∘δ∘γ]