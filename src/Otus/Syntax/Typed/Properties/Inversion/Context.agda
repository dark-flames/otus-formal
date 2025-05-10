{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Context where

open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Presuppositions

open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (_,_ to pair)

record CtxExtInversion ( Γ : Context ) : Set where
  constructor ctxExtInv
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    ⊢Γ≡Γ',A : ⊢ Γ ≡ⱼ Γ' , A

record CtxSplit ( Γ : Context ) : Set where
  constructor ctxExtInv
  field
    Γ₁ : Context
    A : Term
    Γ₂ : Context
    Γ₁⊢A : Γ₁ ⊢ A
    ⊢Γ₁,A⧺Γ₂ : ⊢ Γ₁ , A ⧺ Γ₂
    ⊢Γ≡Γ₁,A⧺Γ₂ : ⊢ Γ ≡ⱼ Γ₁ , A ⧺ Γ₂


record VarExistence ( Γ : Context ) ( x : ℕ ) : Set where
  constructor varExist 
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    Γ⊢dropSx⇒Γ',A : Γ ⊢ drop (suc x) ⇒ Γ'

private
  variable
    Γ Δ Ξ  : Context
    A B : Term

ctxEqExtInversion : ⊢ Γ , A ≡ⱼ Δ , B →  ⊢ Γ ≡ⱼ Δ × Γ ⊢ A ≡ⱼ B
ctxEqExtInversion (CEqRefl ⊢Γ,A) = let 
    pair ⊢Γ Γ⊢A = ctxExtInversion ⊢Γ,A
  in pair (CEqRefl ⊢Γ) (TyEqRefl Γ⊢A)
ctxEqExtInversion (CEqExt ⊢Γ≡Δ _ _ Γ⊢A≡B) = pair ⊢Γ≡Δ Γ⊢A≡B

  