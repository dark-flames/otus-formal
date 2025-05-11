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

infix 1 _begin_

sb-begin_ : (Γ : Context) → Γ ⊢ γ ⇒ Δ 
sb-begin p = Γ⊢A



by-subst : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ A

_end_ : Γ ⊢ A → Γ ⊢ A