{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Inversion.Context where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Relation
open import Otus.Syntax.Typed.Presupposition.Stability
open import Otus.Syntax.Typed.Presupposition.Inversion.Base


open Product

record CtxExtInversion ( Γ : Context ) : Set where
  constructor ctxExtInv
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    ⊢Γ≡Γ'◁A : ⊢ Γ ≡ⱼ Γ' ◁ A


private
  variable
    Γ Δ : Context
    A B : Term

ctxEqExtInversion : ⊢ Γ ◁ A ≡ⱼ Δ ◁ B →  ⊢ Γ ≡ⱼ Δ × Γ ⊢ A ≡ⱼ B
ctxEqExtInversion (CEqExt ⊢Γ≡Δ _ _ Γ⊢A≡B _ _ _) = ⊢Γ≡Δ , Γ⊢A≡B

  