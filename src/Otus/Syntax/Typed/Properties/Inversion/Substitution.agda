{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Substitution where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context



private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term


dropInversion : Γ ⊢ drop (suc x) ⇒ Δ → CtxExtInversion Γ
dropInversion (SbDropˢ Γ⊢dropX⇒Δ Γ⊢A) = let 
    ⊢Γ▷A = ctxExt Γ⊢A
  in ctxExtInv _ _ Γ⊢A (ctxEqRefl ⊢Γ▷A)
dropInversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = dropInversion Γ⊢dropX⇒Δ₁

idInversion : Γ ⊢ idₛ ⇒ Δ → ⊢ Γ ≡ⱼ Δ
idInversion (SbId ⊢Γ) = CEqRefl ⊢Γ
idInversion (SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    ⊢Γ≡Δ₁ = idInversion Γ⊢γ⇒Δ₁
  in ctxEqTrans ⊢Γ≡Δ₁ ⊢Δ₁≡Δ₂

drop1Inversion : Γ ⊢ drop 1 ⇒ Δ 
  → Σ[ inv ∈ CtxExtInversion Γ ] 
    ⊢ (CtxExtInversion.Γ' inv) ≡ⱼ Δ
drop1Inversion Γ⊢drop1⇒Δ@(SbDropˢ Γ⊢id⇒Δ Γ⊢A) = let 
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in dropInversion Γ⊢drop1⇒Δ , ⊢Γ≡Δ
drop1Inversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    inv , ⊢Γ'≡Δ₁ = drop1Inversion Γ⊢dropX⇒Δ₁
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