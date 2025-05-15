{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties


private
  variable
    l : ULevel
    Γ Δ Ξ : Context
    γ γ₁ γ₂ δ : Substitution
    A B C D : Term

-- Type Judgement

Ty-Pi : Γ ▷ A ⊢ B → Γ ⊢ Pi A B
Ty-Pi Γ▷A⊢B = let
    _ , Γ⊢A = ctxExtInversion (tyWfCtx Γ▷A⊢B)
  in TyPi Γ⊢A Γ▷A⊢B

Ty-U : ⊢ Γ → Γ ⊢ U l
Ty-U = TyU

Ty-Subst : Δ ⊢ A → Γ ⊢ γ ⇒ Δ 
    → Γ ⊢ (A [ γ ]ₑ)
Ty-Subst = TySubst

Ty-Russel : Γ ⊢ A ∷ U l
    → Γ ⊢ A
Ty-Russel = TyRussel

-- Definitional Type Equality

TyEq-Pi : Γ ⊢ A ≡ⱼ B → Γ ▷ A ⊢ C ≡ⱼ D
    → Γ ⊢ Pi A C ≡ⱼ Pi B D
TyEq-Pi Γ⊢A≡B Γ▷A⊢C≡D = let
    Γ⊢A , _ = tyEqWf Γ⊢A≡B
  in TyEqPi Γ⊢A Γ⊢A≡B Γ▷A⊢C≡D

TyEq-Subst : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ B [ γ₂ ]ₑ
TyEq-Subst = TyEqSubst

TyEq-Russel : Γ ⊢ A ≡ⱼ B ∷ U l
    → Γ ⊢ A ≡ⱼ B
TyEq-Russel = TyEqRussel

TyEq-PiSubst : Δ ⊢ Pi A B → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Pi A B [ γ ]ₑ ≡ⱼ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ)
TyEq-PiSubst = TyEqPiSubst

TyEq-USubst : Δ ⊢ U l → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ U l [ γ ]ₑ ≡ⱼ U l
TyEq-USubst = TyEqUSubst

TyEq-SubstSubst : Ξ ⊢ A → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢  A [ δ ]ₑ [ γ ]ₑ ≡ⱼ A [ δ ∘ γ ]ₑ
TyEq-SubstSubst = TyEqSubstSubst

TyEq-SubstId : Γ ⊢ A
    → Γ ⊢ A [ idₛ ]ₑ ≡ⱼ A
TyEq-SubstId = TyEqSubstId