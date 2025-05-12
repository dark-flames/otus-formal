{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base

private
  variable
    l l₁ l₂ : ULevel
    x y n : ℕ
    Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ δ₃ ξ : Substitution
    A B C D : Term
    f g a b c d : Term

module TyEqReasoning where
  infix 1 _⊢begin-ty_

  _⊢begin-ty_ : (Γ : Context) →  Γ ⊢ A ≡ⱼ B  → Γ ⊢ A ≡ⱼ B
  Γ ⊢begin-ty aRb = aRb

  infixr 2 ty-step-≡-⟩  ty-step-≡-∣ ty-step-≡-⟨

  ty-step-≡-⟩ : (A : Term) → Γ ⊢ A ≡ⱼ B  → Γ ⊢ B ≡ⱼ C → Γ ⊢ A ≡ⱼ C
  ty-step-≡-⟩ _ = TyEqTrans

  ty-step-≡-∣ : (A : Term) → Γ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
  ty-step-≡-∣ _ aRb = aRb

  ty-step-≡-⟨ : (A : Term) → Γ ⊢ B ≡ⱼ A → Γ ⊢ B ≡ⱼ C → Γ ⊢ A ≡ⱼ C
  ty-step-≡-⟨ _ bRa bRc = TyEqTrans (TyEqSym bRa) bRc

  syntax ty-step-≡-⟩ x xRy yRz  = x ty-≡⟨ xRy ⟩ yRz
  syntax ty-step-≡-∣ x xRy      = x ty-≡⟨⟩ xRy
  syntax ty-step-≡-⟨ x yRx yRz  = x ty-≡⟨ yRx ⟨ yRz
  
  infix 3 ty-step-≡-⟨-∎ ty-step-≡-⟩-∎
  
  ty-step-≡-⟨-∎ : ∀ {Γ} → (A B : Term) → Γ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
  ty-step-≡-⟨-∎ _ _ aRb = aRb

  ty-step-≡-⟩-∎ : ∀ {Γ} → (A B : Term) → Γ ⊢ B ≡ⱼ A → Γ ⊢ A ≡ⱼ B
  ty-step-≡-⟩-∎ _ _ bRa = TyEqSym bRa

  syntax ty-step-≡-⟨-∎ x y xRy = x ty-≡⟨ xRy ⟩∣ y ∎
  syntax ty-step-≡-⟩-∎ x y yRx = x ty-≡⟨ yRx ⟨∣ y ∎