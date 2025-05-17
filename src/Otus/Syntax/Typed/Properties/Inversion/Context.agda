{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Context where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Presupposition

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
ctxEqExtInversion (CEqRefl ⊢Γ◁A) = let 
    ⊢Γ , Γ⊢A = ctxExtInversion ⊢Γ◁A
  in CEqRefl ⊢Γ , TyEqRefl Γ⊢A
ctxEqExtInversion (CEqExt ⊢Γ≡Δ _ _ Γ⊢A≡B) = ⊢Γ≡Δ , Γ⊢A≡B

  