{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.Presuppositions where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ  : Context
    γ δ δ₁ δ₂ : Substitution
    f a b c A B C : Term
open _⊢_⇒_
open ⊢_
open _⊢_

postulate 
    
    tyStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A → Γ ⊢ A
    tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
    substDomainStability : ⊢ Γ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ γ ⇒ Δ
    substComainStability : ⊢ Δ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Γ ⊢ γ ⇒ Ξ
    substComainStability' : ⊢ Δ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
    tyEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B

    {- If Γ ⊢ δ ⇒ Δ then ⊢ Γ and ⊢ Δ -}
    substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
    {- If Γ ⊢ A then ⊢ Γ -}
    tyWfCtx : Γ ⊢ A → ⊢ Γ
    {- If Γ ⊢ a ∷ A then ⊢ Γ -}
    tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
    {- If Γ ⊢ γ ≡ⱼ δ ⇒ Δ then Γ ⊢ γ ⇒ Δ and Γ ⊢ δ ⇒ Δ -}
    substEqWf : Γ ⊢ γ ≡ⱼ δ ⇒ Δ → Γ ⊢ γ ⇒ Δ × Γ ⊢ δ ⇒ Δ
    {- If Γ ⊢ A ≡ⱼ B then Γ ⊢ A and Γ ⊢ B -}
    tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢  B
    {- If Γ ⊢ a ≡ⱼ b ∷ A then Γ ⊢ a ∷ Aand b ∷ B -}
    tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ B
    
tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
---- Context
ctxWeakening :  ⊢ Γ , A → ⊢ Γ
ctxWeakening (CExt ctx _) = ctx

ctxExpand : ⊢ Γ , A → Γ ⊢ A
ctxExpand (CExt _ ty) = ty

ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWf (CEqRefl ⊢Γ) = pair ⊢Γ ⊢Γ
ctxEqWf (CEqSym Γ≡Δ) = swap (ctxEqWf Γ≡Δ)
ctxEqWf (CEqTrans Γ≡Δ Δ≡Ξ) = pair (proj₁ (ctxEqWf Γ≡Δ)) (proj₂ (ctxEqWf Δ≡Ξ))
ctxEqWf (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B) = let (pair ⊢Γ ⊢Δ) = ctxEqWf Γ≡Δ
    in pair (CExt ⊢Γ Γ⊢A) (CExt ⊢Δ Δ⊢B)

-- tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tyStability Γ≡Δ (TyPi Γ⊢A ΓA⊢B) = let Δ⊢A = tyStability Γ≡Δ Γ⊢A
    in let Γ,A≡Δ,A = CEqExt Γ≡Δ Γ⊢A Δ⊢A (TyEqRefl Γ⊢A)
    in let ΔA⊢B = tyStability Γ,A≡Δ,A ΓA⊢B
    in TyPi Δ⊢A ΔA⊢B
tyStability Γ≡Δ  (TyU _) = let (pair _ ⊢Δ) = ctxEqWf Γ≡Δ
    in TyU ⊢Δ
tyStability Γ≡Δ (TySubst Δ⊢A Γ⇒Δ) = let Ξ⇒Δ = substDomainStability Γ≡Δ Γ⇒Δ
    in TySubst Δ⊢A Ξ⇒Δ
tyStability Γ≡Δ (TyRussel Γ⊢A∷U) = TyRussel (tmStability Γ≡Δ Γ⊢A∷U)

---- Substitution
displayMap : Γ ⊢ A → Γ , A ⊢ drop 1 ⇒ Γ
displayMap ΓA = SbDropˢ (SbId (CEqRefl (tyWfCtx ΓA))) (ΓA)

liftSubst : Δ , A ⊢ drop 1 ⇒ Δ → Γ ⊢ γ ⇒ Δ 
    → Γ , (A [ γ ]ₑ) ⊢ (γ ∘ (drop 1)) , Var 0 ⇒ Δ , A
liftSubst display gamma = let ΔA = ctxExpand (proj₁ (substWfCtx display))
    in let ΓA = TySubst ΔA gamma 
---- (Γ , (A [ γ ]ₑ)) ⊢ drop 1 ⇒ Γ
    in let dropSb = displayMap ΓA
---- (Γ , (A [ γ ]ₑ)) ⊢ γ ∘ drop 1 ⇒ Δ
    in let baseSb = SbComp gamma dropSb
---- (Γ , (A [ γ ]ₑ)) ⊢ Var 0 ∷ (A [ γ ∘ drop 1 ]ₑ)
    in let var = TmTyConv (TmVar ΓA) (TyEqSubstSubst ΓA dropSb)
    in SbExt baseSb ΔA var

forward : ⊢ Γ ≡ⱼ Δ → Γ ⊢ idₛ ⇒ Δ
forward = SbId

backward : ⊢ Γ ≡ⱼ Δ → Δ ⊢ idₛ ⇒ Γ
backward Γ≡Δ = SbId (CEqSym Γ≡Δ)

tyEqLift : Γ ⊢ A ≡ⱼ B → Γ ⊢ C → Γ , C ⊢ (A [ drop 1 ]ₑ) ≡ⱼ (B [ drop 1 ]ₑ)
tyEqLift eq eTy = let sb = displayMap eTy
    in TyEqSubst eq (SbEqRefl sb)

tmEqLift : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ C → Γ , C ⊢ (a [ drop 1 ]ₑ) ≡ⱼ (b [ drop 1 ]ₑ) ∷ (A [ drop 1 ]ₑ)
tmEqLift eq eTy = let sb = displayMap eTy
    in TmEqSubst eq (SbEqRefl sb)
     