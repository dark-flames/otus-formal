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
    substComainStability : ⊢ Δ ≡ⱼ Ξ → Γ ⊢ γ ⇒ Δ → Γ ⊢ γ ⇒ Ξ
    

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
tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B

displayMap : Γ ⊢ A → Γ , A ⊢ drop 1 ⇒ Γ
---- Context
ctxWeakening :  ⊢ Γ , A → ⊢ Γ
ctxWeakening (CExt ctx _) = ctx

ctxExpand : ⊢ Γ , A → Γ ⊢ A
ctxExpand (CExt _ ty) = ty

ctxEqSym : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Γ
ctxEqSym (CEqRefl ⊢Γ) = CEqRefl ⊢Γ
ctxEqSym (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) = let Δ≡Γ = ctxEqSym Γ≡Δ
    in CEqExt Δ≡Γ Δ⊢B Γ⊢A (TyEqSym Δ⊢A≡B) (TyEqSym Γ⊢A≡B)


ctxEqTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
ctxEqTrans (CEqRefl ⊢Γ) Γ≡Ξ = Γ≡Ξ
ctxEqTrans Γ≡Ξ (CEqRefl ⊢Ξ) = Γ≡Ξ
ctxEqTrans (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) (CEqExt Δ≡Ξ _ Ξ⊢C Δ⊢B≡C Ξ⊢B≡C) = let Γ≡Ξ = ctxEqTrans Γ≡Δ Δ≡Ξ
    in let Δ⊢A≡C = TyEqTrans Δ⊢A≡B Δ⊢B≡C
    in let Ξ⊢A≡C = tyEqStability Δ≡Ξ Δ⊢A≡C -- todo : may be blocked by tc
    in let Γ⊢A≡C = tyEqStability (ctxEqSym Γ≡Δ) Δ⊢A≡C
    in CEqExt Γ≡Ξ Γ⊢A Ξ⊢C Γ⊢A≡C Ξ⊢A≡C 


ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWf (CEqRefl ⊢Γ) = pair ⊢Γ ⊢Γ
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
substDomainStability Γ≡Ξ (SbId Γ≡Δ) = SbId (ctxEqTrans (ctxEqSym Γ≡Ξ) Γ≡Δ)
substDomainStability (CEqExt Γ≡Ξ Γ⊢A Ξ⊢B Γ⊢A≡B Δ⊢A≡B) (SbDropˢ Γ⇒Δ _) = let Ξ⇒Δ = substDomainStability Γ≡Ξ Γ⇒Δ
    in SbDropˢ Ξ⇒Δ  Ξ⊢B
substDomainStability Γ,A≡Ξ,B (SbExt Γ,A⇒Δ Δ⊢A Γ,A⊢a∷A) = let Ξ,B⇒Δ = substDomainStability Γ,A≡Ξ,B Γ,A⇒Δ
    in SbExt Ξ,B⇒Δ Δ⊢A (tmStability Γ,A≡Ξ,B Γ,A⊢a∷A)
substDomainStability Γ₁≡Δ (SbComp Γ₂⇒Γ₃ Γ₁⇒Γ₂) = let Δ⇒Γ₂ = substDomainStability Γ₁≡Δ Γ₁⇒Γ₂
    in SbComp Γ₂⇒Γ₃ Δ⇒Γ₂

-- tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability (CEqRefl ⊢Γ) Γ⊢a∷A = Γ⊢a∷A
tmStability (CEqExt Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B Δ⊢A≡B) (TmVar _) = let Δ,B⇒Δ = displayMap Δ⊢B
    in let A≡B' = TyEqSubst (TyEqSym Δ⊢A≡B) (SbEqRefl Δ,B⇒Δ)
    in TmTyConv (TmVar Δ⊢B) A≡B'
tmStability Γ≡Δ (TmLam Γ⊢A Γ,A⊢b∷B) = let Δ⊢A = tyStability Γ≡Δ Γ⊢A 
    in let Γ,A≡Δ,A = CEqExt Γ≡Δ Γ⊢A Δ⊢A (TyEqRefl Γ⊢A) (TyEqRefl Δ⊢A)
    in let Δ,A⊢b∷B = tmStability Γ,A≡Δ,A Γ,A⊢b∷B
    in TmLam Δ⊢A Δ,A⊢b∷B
tmStability Γ≡Δ (TmPi Γ⊢A∷U Γ,A⊢B∷U) = let Γ⊢A = TyRussel Γ⊢A∷U
    in let Δ⊢A∷U = tmStability Γ≡Δ Γ⊢A∷U
    in let Δ⊢A = TyRussel Δ⊢A∷U 
    in let Γ,A≡Δ,A = CEqExt Γ≡Δ Γ⊢A Δ⊢A (TyEqRefl Γ⊢A) (TyEqRefl Δ⊢A)
    in let Δ,A⊢B∷U = tmStability Γ,A≡Δ,A Γ,A⊢B∷U
    in TmPi Δ⊢A∷U Δ,A⊢B∷U
tmStability Γ≡Δ (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let Δ⊢f∷PiAB = tmStability Γ≡Δ Γ⊢f∷PiAB
    in let Δ⊢a∷A = tmStability Γ≡Δ Γ⊢a∷A
    in TmApp Δ⊢f∷PiAB Δ⊢a∷A
tmStability Γ≡Δ (TmSubst Ξ⊢a∷A Γ⇒Ξ) = TmSubst Ξ⊢a∷A (substDomainStability Γ≡Δ Γ⇒Ξ)
tmStability Γ≡Δ (TmU _) = let pair _ ⊢Δ = ctxEqWf Γ≡Δ
    in TmU ⊢Δ
tmStability Γ≡Δ (TmTyConv Γ⊢a∷A Γ⊢A≡B) = TmTyConv (tmStability Γ≡Δ Γ⊢a∷A) (tyEqStability Γ≡Δ Γ⊢A≡B)


-- tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqStability (CEqRefl ⊢Γ) Γ⊢A≡B = Γ⊢A≡B
tyEqStability Γ≡Δ (TyEqRefl Γ⊢A) = TyEqRefl (tyStability Γ≡Δ Γ⊢A)
tyEqStability Γ≡Δ (TyEqSym Γ⊢B≡A) = TyEqSym (tyEqStability Γ≡Δ Γ⊢B≡A)

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
backward Γ≡Δ = SbId (ctxEqSym Γ≡Δ)

tyEqLift : Γ ⊢ A ≡ⱼ B → Γ ⊢ C → Γ , C ⊢ (A [ drop 1 ]ₑ) ≡ⱼ (B [ drop 1 ]ₑ)
tyEqLift eq eTy = let sb = displayMap eTy
    in TyEqSubst eq (SbEqRefl sb)

tmEqLift : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ C → Γ , C ⊢ (a [ drop 1 ]ₑ) ≡ⱼ (b [ drop 1 ]ₑ) ∷ (A [ drop 1 ]ₑ)
tmEqLift eq eTy = let sb = displayMap eTy
    in TmEqSubst eq (SbEqRefl sb)
     