{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Substitution where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context

record DropInversion ( Γ : Context ) ( x : ℕ ) : Set where
  constructor dropInv
  field
    Γ' : Context
    Γ⊢dropX⇒Γ' : Γ ⊢ drop x ⇒ Γ'

record DropSucInversion ( Γ Δ : Context ) ( x : ℕ ) : Set where
  constructor dropSucInv
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    ⊢Γ≡Γ'▷A : ⊢ Γ ≡ⱼ Γ' ▷ A
    Γ'⊢dropX⇒Δ : Γ' ⊢ drop x ⇒ Δ
    

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term


dropSucInversion : Γ ⊢ drop (suc x) ⇒ Δ → DropSucInversion Γ Δ x
dropSucInversion (SbDropˢ Γ⊢dropX⇒Δ Γ⊢A) = let 
    ⊢Γ▷A = ctxExt Γ⊢A
  in dropSucInv _ _ Γ⊢A (ctxEqRefl ⊢Γ▷A) Γ⊢dropX⇒Δ
dropSucInversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = let
    dropSucInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A Γ'⊢dropX⇒Δ₁ = dropSucInversion Γ⊢dropX⇒Δ₁
  in dropSucInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A (SbConv Γ'⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂)

idInversion : Γ ⊢ idₛ ⇒ Δ → ⊢ Γ ≡ⱼ Δ
idInversion (SbId ⊢Γ) = CEqRefl ⊢Γ
idInversion (SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    ⊢Γ≡Δ₁ = idInversion Γ⊢γ⇒Δ₁
  in ctxEqTrans ⊢Γ≡Δ₁ ⊢Δ₁≡Δ₂

drop1Inversion : Γ ⊢ drop 1 ⇒ Δ 
  → Σ[ inv ∈ CtxExtInversion Γ ] 
    ⊢ (CtxExtInversion.Γ' inv) ≡ⱼ Δ
drop1Inversion Γ⊢drop1⇒Δ = let 
    dropSucInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A Γ'⊢id⇒Δ₁ = dropSucInversion Γ⊢drop1⇒Δ 
  in ctxExtInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A , (idInversion Γ'⊢id⇒Δ₁)

dropInversion : Γ ⊢ drop x ⇒ Δ
  → Σ[ inv ∈ DropInversion Γ x ]
    ⊢ (DropInversion.Γ' inv) ≡ⱼ Δ
dropInversion Γ⊢γ⇒Γ@(SbId ⊢Γ) = dropInv _ Γ⊢γ⇒Γ , ctxEqRefl ⊢Γ
dropInversion (SbDropˢ Γ⊢dropX⇒Δ Γ⊢A) = let 
    dropInv Γ' Γ⊢dropX⇒Γ' , ⊢Γ'≡Δ = dropInversion Γ⊢dropX⇒Δ
    Γ▷A⊢dropSX⇒Γ' = SbDropˢ Γ⊢dropX⇒Γ' Γ⊢A
  in dropInv Γ' Γ▷A⊢dropSX⇒Γ' , ⊢Γ'≡Δ
dropInversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    inv , ⊢Γ'≡Δ₁ = dropInversion Γ⊢dropX⇒Δ₁
  in inv , (ctxEqTrans ⊢Γ'≡Δ₁ ⊢Δ₁≡Δ₂)

substExtInversion : Γ ⊢ γ ▶ a ⇒ Δ 
  → Σ[ inv ∈ CtxExtInversion Δ ] 
    Γ ⊢ γ ⇒ CtxExtInversion.Γ' inv ×
    Γ ⊢ a ∷ (CtxExtInversion.A inv) [ γ ]ₑ
substExtInversion (SbExt Γ⊢γ⇒Δ Δ⊢A Γ⊢a∷Aγ) = let 
    ⊢Δ▷A = ctxExt Δ⊢A
    inv = ctxExtInv _ _ Δ⊢A (ctxEqRefl ⊢Δ▷A)
  in inv , Γ⊢γ⇒Δ , Γ⊢a∷Aγ
substExtInversion (SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    ctxExtInv Δ A Δ⊢A ⊢Δ₁≡Δ▷A , Γ⊢γ⇒Δ₁ , Γ⊢a∷Aγ = substExtInversion Γ⊢γ⇒Δ₁
    inv = ctxExtInv Δ A Δ⊢A (ctxEqTrans (ctxEqSym ⊢Δ₁≡Δ₂) ⊢Δ₁≡Δ▷A)
  in inv , Γ⊢γ⇒Δ₁ , Γ⊢a∷Aγ