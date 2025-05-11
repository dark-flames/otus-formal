{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.DefEq where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Reasoning
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion
open import Otus.Syntax.Typed.Properties.Substitution

private
  variable
    l l₁ l₂ : ULevel
    Γ Γ' Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term

tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmEqWfTy : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ A
substWfCodomain : Γ ⊢ γ ⇒ Δ → ⊢ Δ
substEqWfCodomain : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Δ

tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A
substEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ

-- tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmWfTy tm with tm
...| TmVarᶻ Γ⊢A = let 
    Γ▷A⊢drop1⇒Γ = displayMap Γ⊢A
  in TySubst Γ⊢A Γ▷A⊢drop1⇒Γ
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = let 
    Γ⊢A = tmWfTy Γ⊢VarX∷A
    Γ▷B⊢drop1⇒Γ = displayMap Γ⊢B
  in TySubst Γ⊢A Γ▷B⊢drop1⇒Γ
...| TmLam Γ⊢A Γ▷A⊢b∷B = TyPi Γ⊢A (tmWfTy Γ▷A⊢b∷B )
...| TmPi Γ⊢A∷U Γ▷A⊢B∷U = TyU (tmWfCtx Γ⊢A∷U)
...| TmApp Γ⊢f∷PiAB Γ⊢a∷A = let 
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
    Γ⊢A , Γ▷A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢id▶a⇒Γ▷A = section Γ⊢A Γ⊢a∷A
  in TySubst Γ▷A⊢B Γ⊢id▶a⇒Γ▷A
...| TmSubst Δ⊢a∷A Γ⇒Δ = let 
    Δ⊢A = tmWfTy Δ⊢a∷A
  in TySubst Δ⊢A Γ⇒Δ
...| TmU ⊢Γ = TyU ⊢Γ
...| TmTyConv _ Γ⊢A≡B = proj₂ (tyEqWf Γ⊢A≡B)

-- substWfCodomain : Γ ⊢ γ ⇒ Δ → ⊢ Δ
substWfCodomain sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⊢dropX⇒Δ _ = substWfCodomain Γ⊢dropX⇒Δ
...| SbExt Γ⊢γ⇒Δ Δ⊢A _ = CExt (substWfCodomain Γ⊢γ⇒Δ) Δ⊢A
...| SbComp Δ⊢δ⇒Ξ _ = substWfCodomain Δ⊢δ⇒Ξ
...| SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)

-- substEqWfCodomain : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Δ
substEqWfCodomain eq with eq
...| SbEqRefl Γ⊢γ⇒Δ = substWfCodomain Γ⊢γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = substEqWfCodomain Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = substEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A _ = CExt (substEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ) Δ⊢A
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ _ = substEqWfCodomain Δ⊢δ₁≡δ₂⇒Ξ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)
...| SbEqCompAssoc Ξ⊢ξ⇒Θ _ _ = substWfCodomain Ξ⊢ξ⇒Θ
...| SbEqIdₗ Δ⊢id⇒Ξ _ = substWfCodomain Δ⊢id⇒Ξ
...| SbEqIdᵣ Δ⊢γ⇒Ξ _ = substWfCodomain Δ⊢γ⇒Ξ
...| SbEqExtVar Γ⊢drop▶var⇒Δ _ = substWfCodomain Γ⊢drop▶var⇒Δ
...| SbEqDropExt Δ⊢drop1⇒Ξ _ = substWfCodomain Δ⊢drop1⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ _ = substWfCodomain Δ⊢dropX⇒Ξ
...| SbEqExtComp Δ⊢δ▶a⇒Ξ _ = substWfCodomain Δ⊢δ▶a⇒Ξ


-- substEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ
substEqWf {Γ}{γ₁} {γ₂} {Δ} eq with eq
...| SbEqRefl Γ⇒Δ = Γ⇒Δ , Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = swap (substEqWf Γ⊢γ₂≡γ₁⇒Δ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ Γ⊢γ₂≡γ₃⇒Δ  = proj₁₂ (substEqWf Γ⊢γ₁≡γ₂⇒Δ) (substEqWf Γ⊢γ₂≡γ₃⇒Δ)
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a≡b∷Aγ₁ = let 
    Γ⊢Aγ₁≡Aγ₂ = tyEqSubst₂ Δ⊢A Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢a∷Aγ₁ , Γ⊢b∷Aγ₁ = tmEqWf Γ⊢a≡b∷Aγ₁
    Γ⊢b∷Aγ₂ = TmTyConv Γ⊢b∷Aγ₁ Γ⊢Aγ₁≡Aγ₂
  in SbExt Γ⊢γ₁⇒Δ Δ⊢A Γ⊢a∷Aγ₁ , SbExt Γ⊢γ₂⇒Δ Δ⊢A Γ⊢b∷Aγ₂
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢δ₁⇒Ξ , Δ⊢δ₂⇒Ξ = substEqWf Δ⊢δ₁≡δ₂⇒Ξ
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in SbComp Δ⊢δ₁⇒Ξ Γ⊢γ₁⇒Δ , SbComp Δ⊢δ₂⇒Ξ Γ⊢γ₂⇒Δ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = let 
    Γ⊢γ₁⇒Δ₁ , Γ⊢γ₂⇒Δ₁ = substEqWf Γ⊢γ₁≡γ₂⇒Δ₁
  in SbConv Γ⊢γ₁⇒Δ₁ ⊢Δ₁≡Δ₂ , SbConv Γ⊢γ₂⇒Δ₁ ⊢Δ₁≡Δ₂
...| SbEqCompAssoc Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let 
    Γ⊢ξ∘δ∘γ⇒Θ = SbComp (SbComp Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
    Γ⊢ξ∘[δ∘γ]⇒Θ = SbComp Ξ⊢ξ⇒Θ  (SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ)
  in Γ⊢ξ∘δ∘γ⇒Θ , Γ⊢ξ∘[δ∘γ]⇒Θ
...| SbEqIdₗ Δ⊢id⇒Ξ Γ⊢γ⇒Δ = let 
    ⊢Δ≡Ξ = idInversion Δ⊢id⇒Ξ
    Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ ⊢Δ≡Ξ
    Γ⊢id∘γ⇒Ξ = SbComp Δ⊢id⇒Ξ Γ⊢γ⇒Δ
  in Γ⊢id∘γ⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqIdᵣ Δ⊢γ⇒Ξ Γ⊢id⇒Δ = let 
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
    Γ⊢γ⇒Ξ = substStability' ⊢Γ≡Δ Δ⊢γ⇒Ξ
    Γ⊢γ∘id⇒Ξ = SbComp Δ⊢γ⇒Ξ Γ⊢id⇒Δ 
  in Γ⊢γ∘id⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqExtVar Γ⊢drop▶var⇒Δ Γ⊢id⇒Δ = Γ⊢drop▶var⇒Δ , Γ⊢id⇒Δ
...| SbEqDropExt Δ⊢drop1⇒Ξ Γ⊢γ▶a⇒Δ = let 
    Γ⊢drop1∘[γ▶a]⇒Ξ = SbComp Δ⊢drop1⇒Ξ Γ⊢γ▶a⇒Δ
    ctxExtInv _ _ Δ'⊢A ⊢Δ≡Δ'▷A , Γ⊢γ⇒Δ' , Γ⊢a∷Aγ = substExtInversion Γ⊢γ▶a⇒Δ
    ctxExtInv _ _ Δ''⊢A ⊢Δ≡Δ''▷A , ⊢Δ''≡Ξ = drop1Inversion Δ⊢drop1⇒Ξ
    ⊢Δ'▷A≡Δ''▷A = ctxEqTrans (ctxEqSym ⊢Δ≡Δ'▷A) ⊢Δ≡Δ''▷A
    ⊢Δ'≡Δ'' = proj₁ (ctxEqExtInversion ⊢Δ'▷A≡Δ''▷A)
    ⊢Δ'≡Ξ = ctxEqTrans ⊢Δ'≡Δ'' ⊢Δ''≡Ξ
    Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ' ⊢Δ'≡Ξ
  in Γ⊢drop1∘[γ▶a]⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ = let 
    Γ⊢dropX∘drop1⇒Ξ = SbComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ
    ctxExtInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A , ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
    Γ'⊢dropX⇒Ξ = substStability' ⊢Γ'≡Δ Δ⊢dropX⇒Ξ
    Γ'▷A⊢dropSX⇒Ξ = SbDropˢ Γ'⊢dropX⇒Ξ Γ'⊢A
    Γ⊢dropSX⇒Ξ = substStability' ⊢Γ≡Γ'▷A Γ'▷A⊢dropSX⇒Ξ
  in Γ⊢dropX∘drop1⇒Ξ , Γ⊢dropSX⇒Ξ
...| SbEqExtComp Δ⊢δ▶a⇒Ξ Γ⊢γ⇒Δ = let 
    Γ⊢[δ▶a]∘γ⇒Ξ = SbComp Δ⊢δ▶a⇒Ξ Γ⊢γ⇒Δ
    ctxExtInv _ _ Ξ'⊢A ⊢Ξ≡Ξ'▷A , Δ⊢δ⇒Ξ' , Δ⊢a∷Aδ = substExtInversion Δ⊢δ▶a⇒Ξ
    Γ⊢δ∘γ⇒Ξ' = SbComp Δ⊢δ⇒Ξ' Γ⊢γ⇒Δ
    Γ⊢aγ∷Aδγ = TmSubst Δ⊢a∷Aδ Γ⊢γ⇒Δ
    Γ⊢Aδγ≡A[δ∘γ] = TyEqSubstSubst Δ⊢δ⇒Ξ' Γ⊢γ⇒Δ Ξ'⊢A
    Γ⊢aγ∷A[δ∘γ] = TmTyConv Γ⊢aγ∷Aδγ Γ⊢Aδγ≡A[δ∘γ]
    Γ⊢[δ∘γ]▶aγ⇒Ξ'▷A = SbExt Γ⊢δ∘γ⇒Ξ' Ξ'⊢A Γ⊢aγ∷A[δ∘γ]
    Γ⊢[δ∘γ]▶aγ⇒Ξ = SbConv Γ⊢[δ∘γ]▶aγ⇒Ξ'▷A (ctxEqSym ⊢Ξ≡Ξ'▷A)
  in Γ⊢[δ▶a]∘γ⇒Ξ , Γ⊢[δ∘γ]▶aγ⇒Ξ 

-- tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
tyEqWf eq with eq
...| TyEqRefl Γ⊢A = Γ⊢A , Γ⊢A
...| TyEqSym Γ⊢B≡A = swap (tyEqWf Γ⊢B≡A)
...| TyEqTrans Γ⊢A≡B Γ⊢B≡C = proj₁₂ (tyEqWf Γ⊢A≡B) (tyEqWf Γ⊢B≡C)
...| TyEqPi Γ⊢A Γ⊢A≡B Γ▷A⊢C≡D = let 
    Γ⊢B = proj₂ (tyEqWf Γ⊢A≡B)
    Γ▷A⊢C , Γ▷A⊢D = tyEqWf Γ▷A⊢C≡D
    ⊢Γ = tyWfCtx Γ⊢A
    ⊢Γ▷A≡Γ▷B = ctxEqExt₂ ⊢Γ Γ⊢A Γ⊢B Γ⊢A≡B
    Γ▷B⊢D = tyStability ⊢Γ▷A≡Γ▷B Γ▷A⊢D
  in TyPi Γ⊢A Γ▷A⊢C , TyPi Γ⊢B Γ▷B⊢D
...| TyEqSubst Δ⊢A≡B Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢A , Δ⊢B = tyEqWf Δ⊢A≡B
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in TySubst Δ⊢A Γ⊢γ₁⇒Δ , TySubst Δ⊢B Γ⊢γ₂⇒Δ
...| TyEqRussel Γ⊢A≡B∷U = let 
    Γ⊢A∷U , Γ⊢B∷U = tmEqWf Γ⊢A≡B∷U
  in TyRussel Γ⊢A∷U , TyRussel Γ⊢B∷U
...| TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ = let 
    Δ⊢A , Δ▷A⊢B = piTyInversion Δ⊢PiAB
    Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ▷Aγ⊢↑γ⇒Δ▷A = liftSubst Γ⊢γ⇒Δ Δ⊢A
    Γ▷Aγ⊢B[↑γ] = TySubst Δ▷A⊢B Γ▷Aγ⊢↑γ⇒Δ▷A
  in TySubst Δ⊢PiAB Γ⊢γ⇒Δ , TyPi Γ⊢Aγ Γ▷Aγ⊢B[↑γ]
...| TyEqUSubst Δ⊢U Γ⊢γ⇒Δ = let 
    ⊢Γ = substWfCtx Γ⊢γ⇒Δ
    ⊢Δ = substWfCodomain Γ⊢γ⇒Δ
  in TySubst (TyU ⊢Δ) Γ⊢γ⇒Δ , TyU ⊢Γ
...| TyEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A = let 
    Γ⊢Aδγ = TySubst (TySubst Ξ⊢A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ 
    Γ⊢δ∘γ⇒Ξ = SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ
    Γ⊢A[δ∘γ] = TySubst Ξ⊢A Γ⊢δ∘γ⇒Ξ
  in Γ⊢Aδγ , Γ⊢A[δ∘γ]
...| TyEqSubstId Γ⊢A = let 
    ⊢Γ = tyWfCtx Γ⊢A
  in TySubst Γ⊢A (SbId ⊢Γ) , Γ⊢A

-- tmEqWfTy : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ A
tmEqWfTy tm with tm
...| TmEqRefl Γ⊢a∷A = tmWfTy Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = tmEqWfTy Γ⊢b≡a∷A
...| TmEqTrans Γ⊢a≡b∷A _ = tmEqWfTy Γ⊢a≡b∷A
...| TmEqLam Γ⊢A Γ▷A⊢a≡b∷B = let 
    Γ▷A⊢B = tmEqWfTy Γ▷A⊢a≡b∷B
  in TyPi Γ⊢A Γ▷A⊢B
...| TmEqPi Γ⊢A _ _ = TyU (tyWfCtx Γ⊢A)
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    Γ⊢A , Γ▷A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢id▶a⇒Γ▷A = section Γ⊢A (proj₁ (tmEqWf Γ⊢a≡b∷A))
  in TySubst Γ▷A⊢B Γ⊢id▶a⇒Γ▷A
...| TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ = let
    Δ⊢A = tmEqWfTy Δ⊢a≡b∷A
    Γ⊢γ₁⇒Δ , _ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in TySubst Δ⊢A Γ⊢γ₁⇒Δ
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let
    _ , Γ⊢B = tyEqWf Γ⊢A≡B
  in Γ⊢B
...| TmEqSubstId Γ⊢a∷A = tmWfTy Γ⊢a∷A
...| TmEqSubstVarExt Δ⊢Var0∷A Γ⊢γ▶a⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢Var0∷A
  in TySubst Δ⊢A Γ⊢γ▶a⇒Δ
...| TmEqSubstVarDrop Δ⊢VarX∷A Γ⊢dropY⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢VarX∷A
  in TySubst Δ⊢A Γ⊢dropY⇒Δ
...| TmEqLamSubst Δ⊢LamA∷PiAB Γ⊢γ⇒Δ = let
    Δ⊢PiAB = tmWfTy Δ⊢LamA∷PiAB
  in TySubst Δ⊢PiAB Γ⊢γ⇒Δ
...| TmEqPiSubst Δ⊢PiAB∷Ul Γ⊢γ⇒Δ = let
    ⊢Γ = substWfCtx Γ⊢γ⇒Δ
  in TyU ⊢Γ
...| TmEqAppSubst Δ⊢f∙a∷A Γ⊢γ⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢f∙a∷A
  in TySubst Δ⊢A Γ⊢γ⇒Δ
...| TmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A = let
    Ξ⊢A = tmWfTy Ξ⊢a∷A
  in TySubst (TySubst Ξ⊢A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
...| TmEqUSubst Γ⊢γ⇒Δ = let
    ⊢Γ = substWfCtx Γ⊢γ⇒Δ
  in TyU ⊢Γ
...| TmEqPiBeta Γ⊢A Γ▷A⊢b∷B Γ⊢a∷A = let
    Γ▷A⊢B = tmWfTy Γ▷A⊢b∷B
    Γ⊢id▶a⇒Γ▷A = section Γ⊢A Γ⊢a∷A
  in TySubst Γ▷A⊢B Γ⊢id▶a⇒Γ▷A
...| TmEqPiEta Γ⊢f∷PiAB = tmWfTy Γ⊢f∷PiAB

-- tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A
tmEqWf eq with eq
...| TmEqRefl Γ⊢a∷A = Γ⊢a∷A , Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = swap (tmEqWf Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = proj₁₂ (tmEqWf Γ⊢a≡b∷A) (tmEqWf Γ⊢b≡c∷A)
...| TmEqLam Γ⊢A Γ▷A⊢a≡b∷B = let 
    Γ▷A⊢a∷B , Γ▷A⊢b∷B = tmEqWf Γ▷A⊢a≡b∷B
  in TmLam Γ⊢A Γ▷A⊢a∷B , TmLam Γ⊢A Γ▷A⊢b∷B
...| TmEqPi Γ⊢A Γ⊢A≡B∷Ul₁ Γ▷A⊢C≡D∷Ul₂ = let 
    Γ⊢A∷Ul₁ , Γ⊢B∷Ul₁ = tmEqWf Γ⊢A≡B∷Ul₁
    Γ▷A⊢C∷Ul₂ , Γ▷A⊢D∷Ul₂ = tmEqWf Γ▷A⊢C≡D∷Ul₂
    Γ⊢A≡B = TyEqRussel Γ⊢A≡B∷Ul₁
    ⊢Γ = tyWfCtx Γ⊢A
    ⊢Γ▷A≡Γ▷B = ctxEqExt₂ ⊢Γ (TyRussel Γ⊢A∷Ul₁) (TyRussel Γ⊢B∷Ul₁) Γ⊢A≡B
    Γ▷B⊢D∷Ul₂ = tmStability ⊢Γ▷A≡Γ▷B Γ▷A⊢D∷Ul₂
  in TmPi Γ⊢A∷Ul₁ Γ▷A⊢C∷Ul₂ , TmPi Γ⊢B∷Ul₁ Γ▷B⊢D∷Ul₂
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    ⊢Γ = tmEqWfCtx Γ⊢f≡g∷PiAB
    Γ⊢f∷PiAB , Γ⊢g∷PiAB = tmEqWf Γ⊢f≡g∷PiAB
    Γ⊢a∷A , Γ⊢b∷A = tmEqWf Γ⊢a≡b∷A
    Γ⊢A , Γ▷A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢a≡b∷Aid = TmEqConv Γ⊢a≡b∷A (TyEqSym (TyEqSubstId Γ⊢A))
    Γ⊢id▶a≡id▶b⇒Γ▷A = substEqExt₂ (SbId ⊢Γ) Γ⊢A Γ⊢a≡b∷Aid
    Γ⊢fa∷B[id▶a] = TmApp Γ⊢f∷PiAB Γ⊢a∷A
    Γ⊢gb∷B[id▶b] = TmApp Γ⊢g∷PiAB Γ⊢b∷A
    Γ⊢B[id▶a]≡B[id▶b] = tyEqSubst₂ Γ▷A⊢B Γ⊢id▶a≡id▶b⇒Γ▷A
    Γ⊢gb∷B[id▶a] = TmTyConv Γ⊢gb∷B[id▶b] (TyEqSym Γ⊢B[id▶a]≡B[id▶b])
  in Γ⊢fa∷B[id▶a] , Γ⊢gb∷B[id▶a]
...| TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢A = tmEqWfTy Δ⊢a≡b∷A
    Δ⊢a∷A , Δ⊢b∷A = tmEqWf Δ⊢a≡b∷A
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢a∷Aγ₁ = TmSubst Δ⊢a∷A Γ⊢γ₁⇒Δ
    Γ⊢b∷Aγ₂ = TmSubst Δ⊢b∷A Γ⊢γ₂⇒Δ
    Γ⊢Aγ₁≡Aγ₂ = tyEqSubst₂ Δ⊢A Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢b∷Aγ₁ = TmTyConv Γ⊢b∷Aγ₂ (TyEqSym Γ⊢Aγ₁≡Aγ₂)
  in Γ⊢a∷Aγ₁ , Γ⊢b∷Aγ₁
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let 
    Γ⊢a∷A , Γ⊢b∷A = tmEqWf Γ⊢a≡b∷A
  in TmTyConv Γ⊢a∷A Γ⊢A≡B , TmTyConv Γ⊢b∷A Γ⊢A≡B
...| TmEqSubstId Γ⊢a∷A = let 
    Γ⊢A = tmWfTy Γ⊢a∷A
    Γ⊢aid∷Aid = TmSubst Γ⊢a∷A (SbId (tmWfCtx Γ⊢a∷A))
    Γ⊢Aid≡A = TyEqSubstId Γ⊢A
    Γ⊢aid∷A = TmTyConv Γ⊢aid∷Aid Γ⊢Aid≡A
  in Γ⊢aid∷A , Γ⊢a∷A
...| TmEqSubstVarExt {Δ} {A} {Γ} {γ} {a} Δ⊢Var0∷A Γ⊢γ▶a⇒Δ = let 
    ctxExtInv Δ₁ B₁ Δ₁⊢B₁ ⊢Δ≡Δ₁▶B₁ , Γ⊢γ⇒Δ₁ , Γ⊢a∷B₁[γ] = substExtInversion Γ⊢γ▶a⇒Δ
    varExist Δ₂ B₂ Δ₂⊢B₂ Δ⊢drop1⇒Δ₂ Δ⊢id⇒Δ₂▶B₂ , Δ⊢A≡B₂[drop1] = varTmInversion Δ⊢Var0∷A
    ⊢Δ≡Δ₂▶B₂ = idInversion Δ⊢id⇒Δ₂▶B₂
    ⊢Δ₁▶B₁≡Δ₂▶B₂ = ctxEqTrans (ctxEqSym ⊢Δ≡Δ₁▶B₁) ⊢Δ≡Δ₂▶B₂
    ⊢Δ₁≡Δ₂ , Δ₁⊢B₁≡B₂ = ctxEqExtInversion ⊢Δ₁▶B₁≡Δ₂▶B₂
    Γ⊢γ▶a⇒Δ₂▶B₂ = SbConv Γ⊢γ▶a⇒Δ ⊢Δ≡Δ₂▶B₂
    Δ₂▶B₂⊢drop⇒Δ₂ = displayMap Δ₂⊢B₂
    Δ₂▶B₂⊢A≡B₂[drop1] = tyEqStability ⊢Δ≡Δ₂▶B₂ Δ⊢A≡B₂[drop1]
    open TyEqReasoning
    Γ⊢A[γ▶a]≡B₁[γ] = 
      Γ ⊢begin
        A [ γ ▶ a ]ₑ
      ≡⟨ tyEqSubst₁ Δ₂▶B₂⊢A≡B₂[drop1] Γ⊢γ▶a⇒Δ₂▶B₂ ⟩
        B₂ [ drop 1 ]ₑ [ γ ▶ a ]ₑ
      ≡⟨ TyEqSubstSubst Δ₂▶B₂⊢drop⇒Δ₂ Γ⊢γ▶a⇒Δ₂▶B₂ Δ₂⊢B₂ ⟩
        B₂ [ (drop 1) ∘ γ ▶ a ]ₑ
      ≡⟨ tyEqSubst₂ Δ₂⊢B₂ (SbEqDropExt Δ₂▶B₂⊢drop⇒Δ₂ Γ⊢γ▶a⇒Δ₂▶B₂) ⟩
        B₂ [ γ ]ₑ
      ≡⟨ tyEqSubst₁ Δ₁⊢B₁≡B₂ Γ⊢γ⇒Δ₁ ⟨|
        B₁ [ γ ]ₑ
      ∎
    Γ⊢a∷A[γ▶a] = TmTyConv Γ⊢a∷B₁[γ] (TyEqSym Γ⊢A[γ▶a]≡B₁[γ])
  in TmSubst Δ⊢Var0∷A Γ⊢γ▶a⇒Δ , Γ⊢a∷A[γ▶a]
...| TmEqSubstVarDrop  {Δ} {x} {A} {Γ} {y}  Δ⊢VarX∷A Γ⊢dropY⇒Δ = let
    varExist Δ₁ B Δ₁⊢B Δ⊢dropSX⇒Δ₁ Δ⊢dropX⇒Δ₁▶B , Δ⊢A≡B[dropSX] = varTmInversion Δ⊢VarX∷A
    Γ⊢dropY+SX⇒Δ₁ , Γ⊢≡dropSX∘dropY≡dropY+SX⇒Δ = dropCompEq Δ⊢dropSX⇒Δ₁ Γ⊢dropY⇒Δ
    Γ⊢VarX[dropY]∷A[dropY] = TmSubst Δ⊢VarX∷A Γ⊢dropY⇒Δ
    open TyEqReasoning
    Γ⊢A[dropY]≡B[dropS[Y+X]] = 
      Γ ⊢begin
        A [ drop y ]ₑ
      ≡⟨ tyEqSubst₁ Δ⊢A≡B[dropSX] Γ⊢dropY⇒Δ ⟩
        B [ drop (1 + x) ]ₑ [ drop y ]ₑ
      ≡⟨ TyEqSubstSubst Δ⊢dropSX⇒Δ₁ Γ⊢dropY⇒Δ Δ₁⊢B ⟩
        B [ drop (1 + x) ∘ drop y ]ₑ
      ≡⟨ tyEqSubst₂ Δ₁⊢B Γ⊢≡dropSX∘dropY≡dropY+SX⇒Δ ⟩
        B [ drop (y + (1 + x))  ]ₑ
      ≡⟨ tyEqSubst₂ Δ₁⊢B (substEqDrop Γ⊢dropY+SX⇒Δ₁ {!   !}) |⟩
        B [ drop (1 + (y + x)) ]ₑ
      ∎
    Γ⊢VarX+Y∷A[dropY] = {!   !}
  in TmSubst Δ⊢VarX∷A Γ⊢dropY⇒Δ , Γ⊢VarX+Y∷A[dropY] 