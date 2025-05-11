{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions


private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term

{-
- Properties independent of context conversion
-}

--- Context

ctxExt : Γ ⊢ A → ⊢ Γ ▷ A
ctxExt Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A

--- Substitution

displayMap : Γ ⊢ A → Γ ▷ A ⊢ drop 1 ⇒ Γ
displayMap Γ⊢A = let 
    ⊢Γ = tyWfCtx Γ⊢A
  in SbDropˢ (SbId ⊢Γ) Γ⊢A

section : Γ ⊢ A → Γ ⊢ a ∷ A → Γ ⊢ idₛ ▶ a ⇒ Γ ▷ A
section Γ⊢A Γ⊢a∷A = let 
    ⊢Γ = tyWfCtx Γ⊢A
    Γ⊢Aid≡A = TyEqSubstId Γ⊢A
    Γ⊢aid∷A = TmTyConv Γ⊢a∷A (TyEqSym Γ⊢Aid≡A)
  in SbExt (SbId ⊢Γ) Γ⊢A Γ⊢aid∷A

liftSubst : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ▷ (A [ γ ]ₑ) ⊢ lift γ ⇒ Δ ▷ A
liftSubst Γ⊢γ⇒Δ Δ⊢A = let 
    Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ▷Aγ⊢drop1⇒Γ = displayMap Γ⊢Aγ
    Γ▷Aγ⊢γ∘drop1⇒Δ = SbComp Γ⊢γ⇒Δ Γ▷Aγ⊢drop1⇒Γ
    Γ▷Aγ⊢Aγdrop≡A[γ∘drop] = TyEqSubstSubst Γ⊢γ⇒Δ Γ▷Aγ⊢drop1⇒Γ Δ⊢A
    Γ▷Aγ⊢Var0∷↑A = TmTyConv (TmVarᶻ Γ⊢Aγ) Γ▷Aγ⊢Aγdrop≡A[γ∘drop]
  in SbExt Γ▷Aγ⊢γ∘drop1⇒Δ Δ⊢A Γ▷Aγ⊢Var0∷↑A



substEqComp₁ : Δ ⊢ δ₁ ≡ⱼ δ₂ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Γ ⊢ δ₁ ∘ γ ≡ⱼ δ₂ ∘ γ ⇒ Ξ
substEqComp₁ Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ⇒Δ = SbEqComp Δ⊢δ₁≡δ₂⇒Ξ (SbEqRefl Γ⊢γ⇒Δ)

substEqComp₂ : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ δ ∘ γ₁ ≡ⱼ δ ∘ γ₂ ⇒ Ξ
substEqComp₂ Δ⊢δ⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = SbEqComp (SbEqRefl Δ⊢δ⇒Ξ) Γ⊢γ₁≡γ₂⇒Δ