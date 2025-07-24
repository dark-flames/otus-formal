{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Reason.Subst where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context

open Product

private
  variable
    x y : ℕ
    Γ Δ Δ₁ Δ₂ Ξ : Context
    γ δ : Substitution
    A a : Term

Sb-Comp :  Δ ⊢ δ ⇒ Ξ × Γ ⊢ γ ⇒ Δ
    → Γ ⊢ δ ∘ γ ⇒ Ξ
Sb-Comp = uncurry SbComp

Sb-Stability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ ⇒ Ξ
    → Δ ⊢ γ ⇒ Ξ
Sb-Stability = sbStability

Sb-Stability' : ⊢ Δ ≡ⱼ Γ → Γ ⊢ γ ⇒ Ξ
    → Δ ⊢ γ ⇒ Ξ
Sb-Stability' = sbStability'

Sb-Conv-by : ⊢ Δ₁ ≡ⱼ Δ₂ → Γ ⊢ γ ⇒ Δ₁ 
    → Γ ⊢ γ ⇒ Δ₂
Sb-Conv-by ⊢Δ₁≡Δ₂ Γ⊢γ⇒Δ₁ = SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂

Sb-Conv-by' : ⊢ Δ₂ ≡ⱼ Δ₁ → Γ ⊢ γ ⇒ Δ₁ 
    → Γ ⊢ γ ⇒ Δ₂
Sb-Conv-by' ⊢Δ₂≡Δ₁ Γ⊢γ⇒Δ₁ = SbConv Γ⊢γ⇒Δ₁ (ctxEqSym ⊢Δ₂≡Δ₁)

Sb-Dropₛ-ext : Γ ⊢ A → Γ ⊢ drop x ⇒ Δ 
        → Γ ◁ A ⊢ drop (1 + x) ⇒ Δ
Sb-Dropₛ-ext Γ⊢A Γ⊢drop-x⇒Δ = SbDropˢ Γ⊢drop-x⇒Δ Γ⊢A

Sb-Ext-to : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ∷ (A [ γ ]ₑ)
        → Γ ⊢ γ ◀ a ⇒ Δ ◁ A
Sb-Ext-to = SbExt
