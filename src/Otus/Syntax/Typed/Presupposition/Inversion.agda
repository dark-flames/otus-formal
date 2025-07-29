{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Inversion where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base

open Product
open PropositionalEq

private
  variable
    l l₁ l₂ : Universe
    Γ Δ  : Context
    a b A B : Term
    γ : Substitution
    
ctxExtInversion : ⊢ Γ ◁ A → ⊢ Γ × Γ ⊢ A
ctxExtInversion (CExt ⊢Γ Γ⊢A) = ⊢Γ , Γ⊢A

univInversion : Γ ⊢ A ∷ Univ l → Universe
univInversion {_} {_} {l} _ = l