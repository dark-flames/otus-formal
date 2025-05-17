{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Context.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

private
  variable
    x y : ℕ
    Γ Δ  : Context
    A B : Term

{-
Binary Logical Relation between Context
-}
infix 4 ⊢_≃_

data ⊢_≃_ : Context → Context → Set where
  CConvEmpty : ⊢ ε ≃ ε
  CConvExt :  ⊢ Γ ≃ Δ
    → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B
    → Δ ⊢ A → Δ ⊢ B → Δ ⊢ A ≡ⱼ B
    → ⊢ Γ ◁ A ≃ Δ ◁ B

ctxConvExtRefl : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A → ⊢ Γ ◁ A ≃ Δ ◁ A
ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A = CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢A (TyEqRefl Γ⊢A) Δ⊢A Δ⊢A (TyEqRefl Δ⊢A)