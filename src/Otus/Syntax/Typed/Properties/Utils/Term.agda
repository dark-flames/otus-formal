{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Utils.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presupposition


private
  variable
    l₁ l₂ : ULevel
    x : ℕ
    Γ Δ : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    A B C D a b : Term

tmTyConv : Γ ⊢ a  ∷ A → Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ∷ B
tmTyConv = TmTyConv

tmTyConv' : Γ ⊢ b ∷ B → Γ ⊢ A ≡ⱼ B
    → Γ ⊢ b ∷ A
tmTyConv' Γ⊢b∷B Γ⊢A≡B = TmTyConv Γ⊢b∷B (TyEqSym Γ⊢A≡B)

tmEqPi₁ : Γ ⊢ A → Γ ⊢ A ≡ⱼ B ∷ Univ l₁ → Γ ◁ A ⊢ C ∷ Univ l₂
    → Γ ⊢ Pi A C ≡ⱼ Pi B C ∷ Univ (l₁ ⊔ l₂)
tmEqPi₁ Γ⊢A Γ⊢A≡B∷Ul₁ Γ◁A⊢C∷Ul₂ = TmEqPi Γ⊢A Γ⊢A≡B∷Ul₁ (TmEqRefl Γ◁A⊢C∷Ul₂)

tmEqPi₂ : Γ ⊢ A ∷ Univ l₁ → Γ ◁ A ⊢ C ≡ⱼ D ∷ Univ l₂
    → Γ ⊢ Pi A C ≡ⱼ Pi A D ∷ Univ (l₁ ⊔ l₂)
tmEqPi₂ Γ⊢A∷Ul₁ Γ◁A⊢C≡D∷Ul₂ = TmEqPi (TyRussel Γ⊢A∷Ul₁) (TmEqRefl Γ⊢A∷Ul₁) Γ◁A⊢C≡D∷Ul₂

tmEqSubst₁ : Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ≡ⱼ b [ γ ]ₑ ∷ A [ γ ]ₑ
tmEqSubst₁ Δ⊢a≡b∷A Γ⊢γ⇒Δ = TmEqSubst Δ⊢a≡b∷A (SbEqRefl Γ⊢γ⇒Δ)

tmEqSubst₂ : Δ ⊢ a ∷ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ a [ γ₁ ]ₑ ≡ⱼ a [ γ₂ ]ₑ ∷ A [ γ₁ ]ₑ
tmEqSubst₂ Δ⊢a∷A Γ⊢γ₁≡γ₂⇒Δ = TmEqSubst (TmEqRefl Δ⊢a∷A) Γ⊢γ₁≡γ₂⇒Δ

tmEqConv : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ A ≡ⱼ B
        → Γ ⊢ a ≡ⱼ b ∷ B
tmEqConv = TmEqConv

tmEqConv' : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ B ≡ⱼ A
        → Γ ⊢ a ≡ⱼ b ∷ B
tmEqConv' Γ⊢a≡b∷A Γ⊢B≡A = TmEqConv Γ⊢a≡b∷A (TyEqSym Γ⊢B≡A)

