{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Context where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context.Base
open import Otus.Syntax.Typed.Properties.Context.Fundamental
open import Otus.Syntax.Typed.Properties.Presupposition

open FunComp

private
  variable
    x : ℕ
    Γ Δ Ξ Θ : Context
    γ γ₁ γ₂ δ : Substitution
    a b c A B C : Term

ctxEqRefl : ⊢ Γ → ⊢ Γ ≡ⱼ Γ
ctxEqRefl = CEqRefl

ctxEqSym : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Γ
ctxEqSym = weakenCtxConv ∘ ctxConvSym ∘ ctxConvFundamental

ctxEqTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
ctxEqTrans ⊢Γ≡Δ ⊢Δ≡Ξ = weakenCtxConv (ctxConvTrans (ctxConvFundamental ⊢Γ≡Δ) (ctxConvFundamental ⊢Δ≡Ξ))

tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tyStability ⊢Γ≡Δ = tyCtxConv (ctxConvFundamental ⊢Γ≡Δ)

tyStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A → Γ ⊢ A 
tyStability' ⊢Γ≡Δ = tyStability (ctxEqSym ⊢Γ≡Δ)

tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability ⊢Γ≡Δ = tmCtxConv (ctxConvFundamental ⊢Γ≡Δ)

tmStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A → Γ ⊢ a ∷ A 
tmStability' ⊢Γ≡Δ = tmStability (ctxEqSym ⊢Γ≡Δ)

sbStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
sbStability ⊢Γ≡Δ = sbCtxConv (ctxConvFundamental ⊢Γ≡Δ)

sbStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ δ ⇒ Ξ
sbStability' ⊢Γ≡Δ = sbStability (ctxEqSym ⊢Γ≡Δ)

tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqStability ⊢Γ≡Δ = tyEqCtxConv (ctxConvFundamental ⊢Γ≡Δ)

tyEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
tyEqStability' ⊢Γ≡Δ = tyEqStability (ctxEqSym ⊢Γ≡Δ)

tmEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
tmEqStability ⊢Γ≡Δ = tmEqCtxConv (ctxConvFundamental ⊢Γ≡Δ)

tmEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
tmEqStability' ⊢Γ≡Δ = tmEqStability (ctxEqSym ⊢Γ≡Δ)

sbEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
sbEqStability ⊢Γ≡Δ = sbEqCtxConv (ctxConvFundamental ⊢Γ≡Δ)

sbEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
sbEqStability' ⊢Γ≡Δ = sbEqStability (ctxEqSym ⊢Γ≡Δ)

ctxEqWfCtx : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWfCtx ⊢Γ≡Δ = ctxConvWf (ctxConvFundamental ⊢Γ≡Δ)
