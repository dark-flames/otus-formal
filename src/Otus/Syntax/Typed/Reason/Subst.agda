{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Subst where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

private
  variable
    l l₁ l₂ : ULevel
    x y n : ℕ
    Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ δ₃ ξ : Substitution
    A B C D : Term
    f g a b c d : Term


Sb-Comp :  Δ ⊢ δ ⇒ Ξ × Γ ⊢ γ ⇒ Δ
    → Γ ⊢ δ ∘ γ ⇒ Ξ
Sb-Comp = uncurry SbComp

module SbEqReasoning where
  infix 1 _⊢begin-sb_

  _⊢begin-sb_ : (Γ : Context) → Γ ⊢ γ₁ ≡ⱼ  γ₂ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  Γ ⊢begin-sb aRb = aRb

  infixr 2 sb-step-≡-⟩  sb-step-≡-∣ sb-step-≡-⟨

  sb-step-≡-⟩ : (γ₁ : Substitution) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
  sb-step-≡-⟩ _ = SbEqTrans

  sb-step-≡-∣ : (γ₁ : Substitution) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ →  Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-∣ _ aRb = aRb

  sb-step-≡-⟨ : (γ₁ : Substitution) → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
  sb-step-≡-⟨ _ bRa bRc = SbEqTrans (SbEqSym bRa) bRc

  syntax sb-step-≡-⟩ x xRy yRz  = x sb-≡⟨ xRy ⟩ yRz
  syntax sb-step-≡-∣ x xRy      = x sb-≡⟨⟩ xRy
  syntax sb-step-≡-⟨ x yRx yRz  = x sb-≡⟨ yRx ⟨ yRz

  infix 3 sb-step-≡-⟨-∎ sb-step-≡-⟩-∎
  
  sb-step-≡-⟨-∎ : ∀ {Γ} → (γ₁ γ₂ : Substitution) → (Δ : Context) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-⟨-∎ _ _ _ aRb = aRb

  sb-step-≡-⟩-∎ : ∀ {Γ} → (γ₁ γ₂ : Substitution) → (Δ : Context) → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-⟩-∎ _ _ _ bRa = SbEqSym bRa

  syntax sb-step-≡-⟨-∎ x y Δ xRy = x sb-≡⟨ xRy ⟩∣ y ∎⇒ Δ
  syntax sb-step-≡-⟩-∎ x y Δ yRx = x sb-≡⟨ yRx ⟨∣ y ∎⇒ Δ
