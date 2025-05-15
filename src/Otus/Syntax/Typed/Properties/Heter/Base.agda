{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Heter.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context


private
  variable
    l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Δ₁ Δ₂ Ξ : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    A B C a b c : Term


-- Heterogeneous term equality
infix 4 _⊢_∷_≡ⱼ_∷_ _⊢_⇒_≡ⱼ_⇒_
data _⊢_∷_≡ⱼ_∷_ : Context → Term → Term → Term → Term → Set where
    HTmEqₗ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
    HTmEqᵣ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B