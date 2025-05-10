{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Substitution where

open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id; _∘_)


private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term


dropInversion : Γ ⊢ drop (suc x) ⇒ Δ → CtxExtInversion Γ
dropInversion (SbDropˢ Γ⊢dropX⇒Δ Γ⊢A) = let 
    pair Γ A = tyInversion Γ⊢A
    ⊢Γ,A = ctxExt Γ⊢A
  in record {
    Γ' = Γ;
    A = A;
    Γ'⊢A = Γ⊢A;
    ⊢Γ≡Γ',A = ctxEqRefl ⊢Γ,A
  }
dropInversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = dropInversion Γ⊢dropX⇒Δ₁

idInversion : Γ ⊢ idₛ ⇒ Δ → ⊢ Γ ≡ⱼ Δ
idInversion (SbId ⊢Γ) = CEqRefl ⊢Γ
idInversion (SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    ⊢Γ≡Δ₁ = idInversion Γ⊢γ⇒Δ₁
  in ctxEqTrans ⊢Γ≡Δ₁ ⊢Δ₁≡Δ₂

drop1Inversion : Γ ⊢ drop 1 ⇒ Δ → Σ[ inv ∈ (CtxExtInversion Γ) ] ⊢ (CtxExtInversion.Γ' inv) ≡ⱼ Δ
drop1Inversion Γ⊢drop1⇒Δ@(SbDropˢ Γ⊢id⇒Δ Γ⊢A) = let 
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in pair (dropInversion Γ⊢drop1⇒Δ)  ⊢Γ≡Δ
drop1Inversion (SbConv Γ⊢dropX⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    pair inv ⊢Γ'≡Δ₁ = drop1Inversion Γ⊢dropX⇒Δ₁
  in pair inv (ctxEqTrans ⊢Γ'≡Δ₁ ⊢Δ₁≡Δ₂)

substExtInversion : Γ ⊢ γ , a ⇒ Δ 
  → Σ[ inv ∈ (CtxExtInversion Δ) ] (Γ ⊢ γ ⇒ (CtxExtInversion.Γ' inv) × Γ ⊢ a ∷ ((CtxExtInversion.A inv) [ γ ]ₑ))
substExtInversion (SbExt Γ⊢γ⇒Δ Δ⊢A Γ⊢a∷Aγ) = let 
    pair Δ A = tyInversion Δ⊢A
    ⊢Δ,A = ctxExt Δ⊢A
    inv = ctxExtInv Δ A Δ⊢A (ctxEqRefl ⊢Δ,A)
  in pair inv (pair Γ⊢γ⇒Δ Γ⊢a∷Aγ)
substExtInversion (SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂) = let 
    pair (ctxExtInv Δ A Δ⊢A ⊢Δ₁≡Δ,A) (pair Γ⊢γ⇒Δ₁ Γ⊢a∷Aγ) = substExtInversion Γ⊢γ⇒Δ₁
    inv = ctxExtInv Δ A Δ⊢A (ctxEqTrans (ctxEqSym ⊢Δ₁≡Δ₂) ⊢Δ₁≡Δ,A)
  in pair inv (pair Γ⊢γ⇒Δ₁ Γ⊢a∷Aγ)