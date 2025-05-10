{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Term where

open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context
open import Otus.Syntax.Typed.Properties.Substitution
open import Otus.Syntax.Typed.Reasoning

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id)

record ULevelConjInversion : Set where
  constructor uLvlConjInv
  field
    l l₁ l₂ : ULevel
    l₁⊔l₂≡l : l₁ ⊔ l₂ ≡ l

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Δ' Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B T : Term

piTmInversion : Γ ⊢ Pi A B ∷ T → Σ[ inv ∈ ULevelConjInversion ] 
    (Γ ⊢ T ≡ⱼ U (ULevelConjInversion.l inv)) ×
      (Γ ⊢ A ∷ U (ULevelConjInversion.l₁ inv)) ×
        (Γ , A ⊢ B ∷ U (ULevelConjInversion.l₂ inv))
piTmInversion (TmPi Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂) = let 
    l₁ = univInversion Γ⊢A∷Ul₁
    l₂ = univInversion Γ,A⊢B∷Ul₂
    ⊢Γ = tmWfCtx Γ⊢A∷Ul₁
    inv = uLvlConjInv (l₁ ⊔ l₂) l₁ l₂ refl
  in pair inv (pair (TyEqRefl (TyU ⊢Γ)) (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂))
piTmInversion (TmTyConv Γ⊢PiAB∷G Γ⊢G≡T) = let 
    pair inv (pair Γ⊢G≡Ul (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂)) = piTmInversion Γ⊢PiAB∷G
    Γ⊢T≡Ul = TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡Ul
  in pair inv (pair Γ⊢T≡Ul (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂))

varTmInversion : Γ ⊢ Var 0 ∷ T → Σ[ inv ∈ CtxExtInversion Γ ]
    (Γ ⊢ T ≡ⱼ ((CtxExtInversion.A inv) [ drop 1 ]ₑ))
varTmInversion (TmVarᶻ Γ⊢A) = let 
    pair Γ A = tyInversion Γ⊢A
    ⊢Γ = tyWfCtx Γ⊢A
    ⊢Γ,A = CExt ⊢Γ Γ⊢A
    inv = ctxExtInv Γ A Γ⊢A (CEqRefl ⊢Γ,A)
    Γ,A⊢drop⇒Γ = displayMap Γ⊢A
    Γ,A⊢A[drop] = TySubst Γ⊢A Γ,A⊢drop⇒Γ
  in pair inv (TyEqRefl Γ,A⊢A[drop])
varTmInversion (TmTyConv Γ⊢var∷G Γ⊢G≡T) = let 
    pair inv Γ⊢G≡A[drop] = varTmInversion Γ⊢var∷G
  in pair inv (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡A[drop])

varTmInversion' : Γ ⊢ Var x ∷ T → Σ[ inv ∈ VarExistence Γ x ]
    (Γ ⊢ T ≡ⱼ ((VarExistence.A inv) [ drop (suc x) ]ₑ))
varTmInversion' (TmVarᶻ {Γ} {A} Γ⊢A) = let 
    Γ,A⊢drop⇒Γ = displayMap Γ⊢A
    inv = varExist Γ A Γ⊢A Γ,A⊢drop⇒Γ
    Γ,A⊢A[drop1] = TySubst Γ⊢A Γ,A⊢drop⇒Γ
  in pair inv (TyEqRefl Γ,A⊢A[drop1])
varTmInversion' (TmVarˢ {Γ} {x} {T} {B} Γ⊢VarX∷T Γ⊢B) = let 
    Γ,B⊢drop⇒Γ = displayMap Γ⊢B
    pair (varExist Γ' A Γ'⊢A Γ⊢dropSx⇒Γ') Γ⊢T≡A[dropSX] = varTmInversion' Γ⊢VarX∷T
    Γ,B⊢dropSSx⇒Γ' = SbDropˢ Γ⊢dropSx⇒Γ' Γ⊢B
    inv = varExist Γ' A Γ'⊢A Γ,B⊢dropSSx⇒Γ'
    open TyEqReasoning
    Γ,B⊢T[drop1]≡A[dropSSX] = 
      Γ , B ⊢begin
        T [ drop 1 ]ₑ
      ≡⟨ TyEqSubst Γ⊢T≡A[dropSX] (SbEqRefl Γ,B⊢drop⇒Γ) ⟩
        A [ drop (1 + x) ]ₑ [ drop 1 ]ₑ
      ≡⟨ (TyEqSubstSubst Γ⊢dropSx⇒Γ' Γ,B⊢drop⇒Γ Γ'⊢A) ⟩
        A [ drop (1 + x) ∘ drop 1 ]ₑ
      ≡⟨ TyEqSubst (TyEqRefl Γ'⊢A) (SbEqDropComp Γ⊢dropSx⇒Γ' Γ,B⊢drop⇒Γ) ∥
        A [ drop (2 + x) ]ₑ
      ∎
  in pair inv Γ,B⊢T[drop1]≡A[dropSSX]
varTmInversion' (TmTyConv Γ⊢VarX∷G Γ⊢G≡T) = let
    pair inv Γ⊢G≡A[dropX] = varTmInversion' Γ⊢VarX∷G
  in pair inv (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡A[dropX])