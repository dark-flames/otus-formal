{-# OPTIONS --without-K --termination-depth=10 #-}
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
    substComainStability : ⊢ Δ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Γ ⊢ γ ⇒ Ξ
    tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B

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
substDomainStability : ⊢ Γ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ γ ⇒ Δ
substDomainStability' : ⊢ Γ ≡ⱼ Ξ → Ξ ⊢ γ ⇒ Δ → Γ ⊢ γ ⇒ Δ
tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A → Γ ⊢ a ∷ A

displayMap : Γ ⊢ A → Γ , A ⊢ drop 1 ⇒ Γ
---- Context
ctxWeakening :  ⊢ Γ , A → ⊢ Γ
ctxWeakening (CExt ctx _) = ctx

ctxExpand : ⊢ Γ , A → Γ ⊢ A
ctxExpand (CExt _ ty) = ty

ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWf (CEqRefl ⊢Γ) = pair ⊢Γ ⊢Γ
ctxEqWf (CEqSym Γ≡Δ) = swap (ctxEqWf Γ≡Δ)
ctxEqWf (CEqTrans Γ≡Δ Δ≡Ξ) = pair (proj₁ (ctxEqWf Γ≡Δ)) (proj₂ (ctxEqWf Δ≡Ξ))
ctxEqWf (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) = let (pair ⊢Γ ⊢Δ) = ctxEqWf Γ≡Δ
    in pair (CExt ⊢Γ Γ⊢A) (CExt ⊢Δ Δ⊢B)

-- tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tyStability Γ≡Δ (TyPi Γ⊢A ΓA⊢B) = let Δ⊢A = tyStability Γ≡Δ Γ⊢A
    in let Γ,A≡Δ,A = CEqExt Γ≡Δ Γ⊢A Δ⊢A (TyEqRefl Γ⊢A) (TyEqRefl Δ⊢A)
    in let ΔA⊢B = tyStability Γ,A≡Δ,A ΓA⊢B
    in TyPi Δ⊢A ΔA⊢B
tyStability Γ≡Δ  (TyU _) = let (pair _ ⊢Δ) = ctxEqWf Γ≡Δ
    in TyU ⊢Δ
tyStability Γ≡Δ (TySubst Δ⊢A Γ⇒Δ) = let Ξ⇒Δ = substDomainStability Γ≡Δ Γ⇒Δ
    in TySubst Δ⊢A Ξ⇒Δ
tyStability Γ≡Δ (TyRussel Γ⊢A∷U) = TyRussel (tmStability Γ≡Δ Γ⊢A∷U)


-- substDomainStability : ⊢ Γ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ γ ⇒ Δ
substDomainStability (CEqRefl ⊢Γ) Γ⇒Δ = Γ⇒Δ
substDomainStability (CEqSym Ξ≡Γ) Γ⇒Δ = substDomainStability' Ξ≡Γ Γ⇒Δ
substDomainStability (CEqTrans Γ≡Δ Δ≡Ξ) γ = substDomainStability Δ≡Ξ (substDomainStability Γ≡Δ γ)
substDomainStability Γ≡Ξ (SbId Γ≡Δ) = SbId (CEqTrans (CEqSym Γ≡Ξ) Γ≡Δ)
substDomainStability (CEqExt Γ≡Ξ Γ⊢A Ξ⊢B Γ⊢A≡B Δ⊢A≡B) (SbDropˢ Γ⇒Δ _) = let Ξ⇒Δ = substDomainStability Γ≡Ξ Γ⇒Δ
    in SbDropˢ Ξ⇒Δ  Ξ⊢B
substDomainStability Γ,A≡Ξ,B (SbExt Γ,A⇒Δ Δ⊢A Γ,A⊢a∷A) = let Ξ,B⇒Δ = substDomainStability Γ,A≡Ξ,B Γ,A⇒Δ
    in SbExt Ξ,B⇒Δ Δ⊢A (tmStability Γ,A≡Ξ,B Γ,A⊢a∷A)
substDomainStability Γ₁≡Δ (SbComp Γ₂⇒Γ₃ Γ₁⇒Γ₂) = let Δ⇒Γ₂ = substDomainStability Γ₁≡Δ Γ₁⇒Γ₂
    in SbComp Γ₂⇒Γ₃ Δ⇒Γ₂

substDomainStability' (CEqRefl ⊢Γ) Ξ⇒Δ = Ξ⇒Δ
substDomainStability' (CEqSym Γ≡Ξ) Ξ⇒Δ = substDomainStability Γ≡Ξ Ξ⇒Δ
substDomainStability' (CEqTrans Γ≡Δ Δ≡Ξ) s = substDomainStability' Γ≡Δ (substDomainStability' Δ≡Ξ s)
substDomainStability' Γ≡Ξ (SbId Ξ≡Δ) = SbId (CEqTrans Γ≡Ξ Ξ≡Δ)
substDomainStability' (CEqExt Γ≡Ξ Γ⊢A Ξ⊢B Γ⊢A≡B Δ⊢A≡B) (SbDropˢ Ξ⇒Δ _) = let Γ⇒Δ = substDomainStability' Γ≡Ξ Ξ⇒Δ
    in SbDropˢ Γ⇒Δ Γ⊢A
substDomainStability' Γ,A≡Ξ,B (SbExt Ξ,B⇒Δ Δ⊢B Γ,B⊢b∷B) = let Γ,A⇒Δ = substDomainStability' Γ,A≡Ξ,B Ξ,B⇒Δ
    in SbExt Γ,A⇒Δ Δ⊢B (tmStability' Γ,A≡Ξ,B Γ,B⊢b∷B)
substDomainStability' Γ≡Δ₁ (SbComp Δ₂⇒Δ₃ Δ₁⇒Δ₂) = let Γ⇒Δ₂ = substDomainStability' Γ≡Δ₁ Δ₁⇒Δ₂
    in SbComp Δ₂⇒Δ₃ Γ⇒Δ₂

-- tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability (CEqRefl ⊢Γ) Γ⊢a∷A = Γ⊢a∷A
tmStability (CEqSym Γ≡Δ) Γ⊢a∷A = tmStability' Γ≡Δ Γ⊢a∷A
tmStability (CEqTrans Γ≡Δ Δ≡Ξ) Γ⊢a∷A = tmStability Δ≡Ξ (tmStability Γ≡Δ Γ⊢a∷A)
tmStability (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) (TmVar _) = let Δ,B⇒Δ = displayMap Δ⊢B
    in let A≡B' = TyEqSubst (TyEqSym Δ⊢A≡B) (SbEqRefl Δ,B⇒Δ)
    in TmTyConv (TmVar Δ⊢B) A≡B'
tmStability Γ≡Δ (TmLam Γ⊢A Γ,A⊢b∷B) = let Δ⊢A = tyStability Γ≡Δ Γ⊢A 
    in let Γ,A≡Δ,A = CEqExt Γ≡Δ Γ⊢A Δ⊢A (TyEqRefl Γ⊢A) (TyEqRefl Δ⊢A)
    in let Δ,A⊢b∷B = tmStability Γ,A≡Δ,A Γ,A⊢b∷B
    in TmLam Δ⊢A Δ,A⊢b∷B

-- tmStability : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A → Γ ⊢ a ∷ A
tmStability' (CEqRefl ⊢Γ) Γ⊢a∷A = Γ⊢a∷A
tmStability' (CEqSym Δ≡Γ) Δ⊢a∷A = tmStability Δ≡Γ Δ⊢a∷A
tmStability' (CEqTrans Γ≡Δ Δ≡Ξ) Ξ⊢a∷A = tmStability' Γ≡Δ (tmStability' Δ≡Ξ Ξ⊢a∷A)
tmStability' (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) (TmVar _) = let Γ,A⇒Γ = displayMap Γ⊢A
    in let A≡B' = TyEqSubst Γ⊢A≡B (SbEqRefl Γ,A⇒Γ)
    in TmTyConv (TmVar Γ⊢A) A≡B'

---- Substitution
-- displayMap : Γ ⊢ A → Γ , A ⊢ drop 1 ⇒ Γ
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
     