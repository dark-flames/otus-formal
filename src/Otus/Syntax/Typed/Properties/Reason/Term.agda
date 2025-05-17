{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Reason.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ : Context
    γ : Substitution
    A B C : Term
    f a b c : Term


-- tactics

Tm-Varᶻ : Γ ⊢ A
    → Γ ◁ A ⊢ Var 0 ∷ A [ drop 1 ]ₑ
Tm-Varᶻ = TmVarᶻ

Tm-Varˢ : Γ ⊢ Var x ∷ A × Γ ⊢ B
    → Γ ◁ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
Tm-Varˢ = uncurry TmVarˢ

Tm-Var-ext : Γ ⊢ B → Γ ⊢ Var x ∷ A
    → Γ ◁ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
Tm-Var-ext Γ⊢B Γ⊢Var-x∷A = TmVarˢ Γ⊢Var-x∷A Γ⊢B

Tm-Lam : (Γ ⊢ A) × (Γ ◁ A ⊢ b ∷ B)
    → Γ ⊢ Lam b ∷ Pi A B
Tm-Lam  = uncurry TmLam

Tm-Lam-abs : Γ ⊢ A → Γ ◁ A ⊢ b ∷ B
    → Γ ⊢ Lam b ∷ Pi A B
Tm-Lam-abs  = TmLam

Tm-Pi : Γ ⊢ A ∷ U l₁ × Γ ◁ A ⊢ B ∷ U l₂
    → Γ ⊢ Pi A B ∷ U (l₁ ⊔ l₂)
Tm-Pi = uncurry TmPi

Tm-App : Γ ⊢ f ∷ Pi A B × Γ ⊢ a ∷ A
    → Γ ⊢ f ∙ a ∷ B [ idₛ ◀ a ]ₑ
Tm-App = uncurry TmApp

Tm-App-on : Γ ⊢ a ∷ A → Γ ⊢ f ∷ Pi A B
    → Γ ⊢ f ∙ a ∷ B [ idₛ ◀ a ]ₑ
Tm-App-on Γ⊢a∷A Γ⊢f∷PiAB = TmApp Γ⊢f∷PiAB Γ⊢a∷A

Tm-Subst : Δ ⊢ a ∷ A × Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst = uncurry TmSubst

Tm-Subst-by : Γ ⊢ γ ⇒ Δ → Δ ⊢ a ∷ A
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst-by Γ⊢γ⇒Δ Δ⊢a∷A = TmSubst Δ⊢a∷A Γ⊢γ⇒Δ

Tm-Subst-on : Δ ⊢ a ∷ A → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst-on = TmSubst

Tm-U : ⊢ Γ 
    → Γ ⊢ U l ∷ U (lsuc l) 
Tm-U = TmU

Tm-TyConv : Γ ⊢ a ∷ A × Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ∷ B
Tm-TyConv = uncurry TmTyConv

Tm-TyConv-by : Γ ⊢ A ≡ⱼ B →  Γ ⊢ a ∷ A
    → Γ ⊢ a ∷ B
Tm-TyConv-by Γ⊢A≡B Γ⊢a∷A = tmTyConv Γ⊢a∷A Γ⊢A≡B

Tm-TyConv-by' : Γ ⊢ B ≡ⱼ A →  Γ ⊢ a ∷ A
    → Γ ⊢ a ∷ B
Tm-TyConv-by' Γ⊢B≡A Γ⊢a∷A = tmTyConv' Γ⊢a∷A Γ⊢B≡A 

Tm-TyConv-on : Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ∷ B
Tm-TyConv-on = TmTyConv

Tm-TyConv-on' : Γ ⊢ a ∷ A → Γ ⊢ B ≡ⱼ A
    → Γ ⊢ a ∷ B
Tm-TyConv-on' Γ⊢a∷A Γ⊢B≡A = TmTyConv Γ⊢a∷A (TyEqSym Γ⊢B≡A)

Tm-Stability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A
    → Δ ⊢ a ∷ A
Tm-Stability = tmStability

Tm-Stability' : ⊢ Δ ≡ⱼ Γ → Γ ⊢ a ∷ A
    → Δ ⊢ a ∷ A
Tm-Stability' = tmStability'






