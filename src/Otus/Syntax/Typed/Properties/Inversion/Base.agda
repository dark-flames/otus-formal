{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

private
  variable
    l : ULevel
    Γ Δ  : Context
    a A B : Term
    γ : Substitution
    
ctxExtInversion : ⊢ Γ ▷ A → ⊢ Γ × Γ ⊢ A
ctxExtInversion (CExt ⊢Γ Γ⊢A) = ⊢Γ , Γ⊢A

univInversion : Γ ⊢ A ∷ U l → ULevel
univInversion {_} {_} {l} _ = l