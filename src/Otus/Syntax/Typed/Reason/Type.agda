{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_; _⊔_; lsuc)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties


private
  variable
    Γ : Context
    γ : Substitution
    A B : Term

Ty-Pi : Γ ▷ A ⊢ B → Γ ⊢ Pi A B
Ty-Pi Γ▷A⊢B = let
    _ , Γ⊢A = ctxExtInversion (tyWfCtx Γ▷A⊢B)
  in TyPi Γ⊢A Γ▷A⊢B

