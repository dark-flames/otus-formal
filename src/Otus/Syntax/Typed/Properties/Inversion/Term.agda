{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context
open import Otus.Syntax.Typed.Reasoning

record ULevelConjInversion : Set where
  constructor uLvlConjInv
  field
    l l₁ l₂ : ULevel
    l₁⊔l₂≡l : l₁ ⊔ l₂ ≡ l

record VarExistence ( Γ : Context ) ( x : ℕ ) : Set where
  constructor varExist 
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    Γ⊢dropSX⇒Γ' : Γ ⊢ drop (suc x) ⇒ Γ'
    Γ⊢dropX⇒Γ'▷A : Γ ⊢ drop x ⇒ Γ' ▷ A

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Δ' Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B T : Term

piTmInversion : Γ ⊢ Pi A B ∷ T 
  → Σ[ inv ∈ ULevelConjInversion ] 
    (Γ ⊢ T ≡ⱼ U (ULevelConjInversion.l inv)) ×
    (Γ ⊢ A ∷ U (ULevelConjInversion.l₁ inv)) ×
    (Γ ▷ A ⊢ B ∷ U (ULevelConjInversion.l₂ inv))
piTmInversion (TmPi Γ⊢A∷Ul₁ Γ▷A⊢B∷Ul₂) = let 
    l₁ = univInversion Γ⊢A∷Ul₁
    l₂ = univInversion Γ▷A⊢B∷Ul₂
    ⊢Γ = tmWfCtx Γ⊢A∷Ul₁
    inv = uLvlConjInv (l₁ ⊔ l₂) l₁ l₂ refl
  in inv , TyEqRefl (TyU ⊢Γ) , Γ⊢A∷Ul₁ , Γ▷A⊢B∷Ul₂
piTmInversion (TmTyConv Γ⊢PiAB∷G Γ⊢G≡T) = let 
    inv , Γ⊢G≡Ul , Γ⊢A∷Ul₁ , Γ▷A⊢B∷Ul₂ = piTmInversion Γ⊢PiAB∷G
    Γ⊢T≡Ul = TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡Ul
  in inv , Γ⊢T≡Ul , Γ⊢A∷Ul₁ , Γ▷A⊢B∷Ul₂
varTmInversion : Γ ⊢ Var x ∷ T 
  → Σ[ inv ∈ VarExistence Γ x ]
    Γ ⊢ T ≡ⱼ (VarExistence.A inv) [ drop (suc x) ]ₑ
varTmInversion (TmVarᶻ Γ⊢A) = let 
    Γ▷A⊢drop⇒Γ = displayMap Γ⊢A
    ⊢Γ▷A = ctxExt Γ⊢A
    inv = varExist _ _ Γ⊢A Γ▷A⊢drop⇒Γ (SbId ⊢Γ▷A) 
    Γ▷A⊢A[drop1] = TySubst Γ⊢A Γ▷A⊢drop⇒Γ
  in inv , TyEqRefl Γ▷A⊢A[drop1]
varTmInversion (TmVarˢ {Γ} {x} {T} {B} Γ⊢VarX∷T Γ⊢B) = let 
    Γ▷B⊢drop⇒Γ = displayMap Γ⊢B
    varExist Γ' A Γ'⊢A Γ⊢dropSX⇒Γ' Γ⊢dropX⇒Γ'▷A , Γ⊢T≡A[dropSX] = varTmInversion Γ⊢VarX∷T
    Γ▷B⊢dropSX⇒Γ'▷A = SbDropˢ Γ⊢dropX⇒Γ'▷A Γ⊢B
    Γ▷B⊢dropSSX⇒Γ' = SbDropˢ Γ⊢dropSX⇒Γ' Γ⊢B
    inv = varExist Γ' A Γ'⊢A Γ▷B⊢dropSSX⇒Γ' Γ▷B⊢dropSX⇒Γ'▷A
    open TyEqReasoning
    Γ▷B⊢T[drop1]≡A[dropSSX] = 
      Γ ▷ B ⊢begin
        T [ drop 1 ]ₑ
      ≡⟨ tyEqSubst₁ Γ⊢T≡A[dropSX] Γ▷B⊢drop⇒Γ ⟩
        A [ drop (1 + x) ]ₑ [ drop 1 ]ₑ
      ≡⟨ TyEqSubstSubst Γ⊢dropSX⇒Γ' Γ▷B⊢drop⇒Γ Γ'⊢A ⟩
        A [ drop (1 + x) ∘ drop 1 ]ₑ
      ≡⟨ tyEqSubst₂ Γ'⊢A (SbEqDropComp Γ⊢dropSX⇒Γ' Γ▷B⊢drop⇒Γ) |⟩
        A [ drop (2 + x) ]ₑ
      ∎
  in inv , Γ▷B⊢T[drop1]≡A[dropSSX]
varTmInversion (TmTyConv Γ⊢VarX∷G Γ⊢G≡T) = let
    inv , Γ⊢G≡A[dropX] = varTmInversion Γ⊢VarX∷G
  in inv , (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡A[dropX]) 