{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Inversion.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base

open Product
open PropositionalEq

private
  variable
    u u₁ u₂ : Universe
    Γ Δ  : Context
    A B : Type
    a b : Term
    γ : Substitution
    
ctxExtInversion : ⊢ Γ ◁ A → ⊢ Γ × Γ ⊢ A
ctxExtInversion (CExt ⊢Γ Γ⊢A) = ⊢Γ , Γ⊢A

univOf : Γ ⊢ A ∷ Univ u → Universe
univOf {_} {_} {u} _ = u