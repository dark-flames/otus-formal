{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Utils.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions

private
  variable
    l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    A B C D : Term

tyEqPi₁ : Γ ⊢ A → Γ ⊢ A ≡ⱼ B → Γ ▷ A ⊢ C
    → Γ ⊢ Pi A C ≡ⱼ Pi B C
tyEqPi₁ Γ⊢A Γ⊢A≡B Γ▷A⊢C = TyEqPi Γ⊢A Γ⊢A≡B (TyEqRefl Γ▷A⊢C)

tyEqPi₂ : Γ ⊢ A → Γ ▷ A ⊢ C ≡ⱼ D
    → Γ ⊢ Pi A C ≡ⱼ Pi A D
tyEqPi₂ Γ⊢A Γ▷A⊢C≡D = TyEqPi Γ⊢A (TyEqRefl Γ⊢A) Γ▷A⊢C≡D

tyEqSubst₁ : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ A [ γ ]ₑ ≡ⱼ B [ γ ]ₑ
tyEqSubst₁ Δ⊢A≡B Γ⊢γ⇒Δ = TyEqSubst Δ⊢A≡B (SbEqRefl Γ⊢γ⇒Δ)

tyEqSubst₂ : Δ ⊢ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ A [ γ₂ ]ₑ
tyEqSubst₂ Δ⊢A Γ⊢γ₁≡γ₂⇒Δ = TyEqSubst (TyEqRefl Δ⊢A) Γ⊢γ₁≡γ₂⇒Δ

tyUnivCong : ⊢ Γ → l₁ ≡ l₂ → Γ ⊢ U l₁ ≡ⱼ U l₂
tyUnivCong ⊢Γ refl = TyEqRefl (TyU ⊢Γ)