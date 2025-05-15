{-# OPTIONS --without-K  --safe #-}
module Otus.Syntax.Typed.Properties.Core where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Reason
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion
open import Otus.Syntax.Typed.Properties.Subst

private
  variable
    Γ Δ : Context
    γ γ₁ γ₂ : Substitution
    f a b A B T : Term

tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmEqWfTy : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ A

tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A
sbEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ

lamTmInversion : Γ ⊢ Lam a ∷ T
  → Σ[ A ∈ Term ] Σ[ B ∈ Term ]
    (Γ ⊢ A) ×
    (Γ ▷ A ⊢ B) ×
    (Γ ⊢ T ≡ⱼ Pi A B) ×
    (Γ ▷ A ⊢ a ∷ B)
lamTmInversion (TmLam Γ⊢A Γ▷A⊢a∷B) = let
    Γ▷A⊢B = tmWfTy Γ▷A⊢a∷B
    Γ⊢PiAB = TyPi Γ⊢A Γ▷A⊢B
  in _ , _ , Γ⊢A , Γ▷A⊢B , TyEqRefl Γ⊢PiAB , Γ▷A⊢a∷B
lamTmInversion (TmTyConv Γ⊢Lam-a∷G Γ⊢G≡T) = let
    _ , _ , Γ⊢A , Γ▷A⊢B , Γ⊢G≡PiAB , Γ▷A⊢b∷B = lamTmInversion Γ⊢Lam-a∷G
  in _ , _ , Γ⊢A , Γ▷A⊢B , (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡PiAB) , Γ▷A⊢b∷B

appTmInversion : Γ ⊢ f ∙ a ∷ T
  → Σ[ A ∈ Term ] Σ[ B ∈ Term ]
    (Γ ⊢ Pi A B) × 
    (Γ ⊢ f ∷ Pi A B) ×
    (Γ ⊢ a ∷ A) ×
    (Γ ⊢ T ≡ⱼ B [ idₛ ▶ a ]ₑ)
appTmInversion Γ⊢f∙a∷T@(TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
  in _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , (TyEqRefl (tmWfTy Γ⊢f∙a∷T))
appTmInversion (TmTyConv Γ⊢f∙a∷G Γ⊢G≡T) = let
    _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , Γ⊢G≡B[id▶a] = appTmInversion Γ⊢f∙a∷G
  in _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡B[id▶a]

-- tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmWfTy tm with tm
...| TmVarᶻ Γ⊢A = let 
    Γ▷A⊢drop1⇒Γ = display Γ⊢A
  in TySubst Γ⊢A Γ▷A⊢drop1⇒Γ
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = let 
    Γ⊢A = tmWfTy Γ⊢VarX∷A
    Γ▷B⊢drop1⇒Γ = display Γ⊢B
  in TySubst Γ⊢A Γ▷B⊢drop1⇒Γ
...| TmLam Γ⊢A Γ▷A⊢b∷B = TyPi Γ⊢A (tmWfTy Γ▷A⊢b∷B)
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


-- sbEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ
sbEqWf {Γ}{γ₁} {γ₂} {Δ} eq with eq
...| SbEqRefl Γ⇒Δ = Γ⇒Δ , Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = swap (sbEqWf Γ⊢γ₂≡γ₁⇒Δ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ Γ⊢γ₂≡γ₃⇒Δ  = proj₁₂ (sbEqWf Γ⊢γ₁≡γ₂⇒Δ) (sbEqWf Γ⊢γ₂≡γ₃⇒Δ)
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a≡b∷Aγ₁ = let 
    Γ⊢Aγ₁≡Aγ₂ = tyEqSubst₂ Δ⊢A Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢a∷Aγ₁ , Γ⊢b∷Aγ₁ = tmEqWf Γ⊢a≡b∷Aγ₁
    Γ⊢b∷Aγ₂ = TmTyConv Γ⊢b∷Aγ₁ Γ⊢Aγ₁≡Aγ₂
  in SbExt Γ⊢γ₁⇒Δ Δ⊢A Γ⊢a∷Aγ₁ , SbExt Γ⊢γ₂⇒Δ Δ⊢A Γ⊢b∷Aγ₂
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢δ₁⇒Ξ , Δ⊢δ₂⇒Ξ = sbEqWf Δ⊢δ₁≡δ₂⇒Ξ
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
  in SbComp Δ⊢δ₁⇒Ξ Γ⊢γ₁⇒Δ , SbComp Δ⊢δ₂⇒Ξ Γ⊢γ₂⇒Δ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = let 
    Γ⊢γ₁⇒Δ₁ , Γ⊢γ₂⇒Δ₁ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ₁
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
    Γ⊢γ⇒Ξ = sbStability' ⊢Γ≡Δ Δ⊢γ⇒Ξ
    Γ⊢γ∘id⇒Ξ = SbComp Δ⊢γ⇒Ξ Γ⊢id⇒Δ 
  in Γ⊢γ∘id⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqExtVar {Γ} {A} Γ⊢Var0∷A = let
    varExist Γ' B Γ'⊢B Γ⊢drop1⇒Γ' Γ⊢id⇒Γ'▷B , Γ⊢A≡B[drop1] = varTmInversion Γ⊢Var0∷A
    ⊢Γ = tmWfCtx Γ⊢Var0∷A
    ⊢Γ≡Γ'▷B = idInversion Γ⊢id⇒Γ'▷B
  in (
      begin
        intro-⟨ Γ⊢Var0∷A ⟩
        Γ ⊢ Var 0 ∷ A
      ⎯⎯⎯⎯⟨ Tm-TyConv-by Γ⊢A≡B[drop1] ⟩
        Γ ⊢ Var 0 ∷ B [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ SbExt Γ⊢drop1⇒Γ' Γ'⊢B  ⟩
        Γ ⊢ drop 1 ▶ Var 0 ⇒ Γ' ▷ B
      ⎯⎯⎯⎯⟨ Sb-Conv-by' ⊢Γ≡Γ'▷B  ⟩
        Γ ⊢ drop 1 ▶ Var 0 ⇒ Γ
      ∎
    ) , (SbId ⊢Γ)
...| SbEqDropExt Δ⊢drop1⇒Ξ Γ⊢γ▶a⇒Δ = let 
    Γ⊢drop1∘[γ▶a]⇒Ξ = SbComp Δ⊢drop1⇒Ξ Γ⊢γ▶a⇒Δ
    ctxExtInv _ _ Δ'⊢A ⊢Δ≡Δ'▷A , Γ⊢γ⇒Δ' , Γ⊢a∷Aγ = sbExtInversion Γ⊢γ▶a⇒Δ
    ctxExtInv _ _ Δ''⊢A ⊢Δ≡Δ''▷A , ⊢Δ''≡Ξ = drop1Inversion Δ⊢drop1⇒Ξ
    ⊢Δ'▷A≡Δ''▷A = ctxEqTrans (ctxEqSym ⊢Δ≡Δ'▷A) ⊢Δ≡Δ''▷A
    ⊢Δ'≡Δ'' = proj₁ (ctxEqExtInversion ⊢Δ'▷A≡Δ''▷A)
    ⊢Δ'≡Ξ = ctxEqTrans ⊢Δ'≡Δ'' ⊢Δ''≡Ξ
    Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ' ⊢Δ'≡Ξ
  in Γ⊢drop1∘[γ▶a]⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ = let 
    Γ⊢dropX∘drop1⇒Ξ = SbComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ
    ctxExtInv _ _ Γ'⊢A ⊢Γ≡Γ'▷A , ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
    Γ'⊢dropX⇒Ξ = sbStability' ⊢Γ'≡Δ Δ⊢dropX⇒Ξ
    Γ'▷A⊢dropSX⇒Ξ = SbDropˢ Γ'⊢dropX⇒Ξ Γ'⊢A
    Γ⊢dropSX⇒Ξ = sbStability' ⊢Γ≡Γ'▷A Γ'▷A⊢dropSX⇒Ξ
  in Γ⊢dropX∘drop1⇒Ξ , Γ⊢dropSX⇒Ξ
...| SbEqExtComp {Δ} {δ} {a} {Ξ} {Γ} {γ} Δ⊢δ▶a⇒Ξ Γ⊢γ⇒Δ = let 
    ctxExtInv Ξ₁ A Ξ₁⊢A ⊢Ξ≡Ξ₁▷A , Δ⊢δ⇒Ξ₁ , Δ⊢a∷Aδ = sbExtInversion Δ⊢δ▶a⇒Ξ
  in (SbComp Δ⊢δ▶a⇒Ξ Γ⊢γ⇒Δ) , (
      begin
        intro-⟨ Δ⊢a∷Aδ ⟩
        Δ ⊢ a ∷ A [ δ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢γ⇒Δ ⟩
        Γ ⊢ a [ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Δ⊢δ⇒Ξ₁ Γ⊢γ⇒Δ Ξ₁⊢A) ⟩
        Γ ⊢ a [ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
      ⎯⎯⎯⎯⟨ Sb-Ext-to (SbComp Δ⊢δ⇒Ξ₁ Γ⊢γ⇒Δ) Ξ₁⊢A ⟩
        Γ ⊢ (δ ∘ γ) ▶ a [ γ ]ₑ  ⇒ Ξ₁ ▷ A
      ⎯⎯⎯⎯⟨ Sb-Conv-by' ⊢Ξ≡Ξ₁▷A ⟩
        Γ ⊢ (δ ∘ γ) ▶ a [ γ ]ₑ  ⇒ Ξ
      ∎
    ) 


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
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
  in TySubst Δ⊢A Γ⊢γ₁⇒Δ , TySubst Δ⊢B Γ⊢γ₂⇒Δ
...| TyEqRussel Γ⊢A≡B∷U = let 
    Γ⊢A∷U , Γ⊢B∷U = tmEqWf Γ⊢A≡B∷U
  in TyRussel Γ⊢A∷U , TyRussel Γ⊢B∷U
...| TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ = let 
    Δ⊢A , Δ▷A⊢B = piTyInversion Δ⊢PiAB
    Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ▷Aγ⊢↑γ⇒Δ▷A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ▷Aγ⊢B[↑γ] = TySubst Δ▷A⊢B Γ▷Aγ⊢↑γ⇒Δ▷A
  in TySubst Δ⊢PiAB Γ⊢γ⇒Δ , TyPi Γ⊢Aγ Γ▷Aγ⊢B[↑γ]
...| TyEqUSubst Δ⊢U Γ⊢γ⇒Δ = let 
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
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
    Γ⊢γ₁⇒Δ , _ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
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
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyU ⊢Γ
...| TmEqAppSubst Δ⊢f∙a∷A Γ⊢γ⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢f∙a∷A
  in TySubst Δ⊢A Γ⊢γ⇒Δ
...| TmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A = let
    Ξ⊢A = tmWfTy Ξ⊢a∷A
  in TySubst (TySubst Ξ⊢A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
...| TmEqUSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
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
    Γ⊢a≡b∷Aid = tmEqConv' Γ⊢a≡b∷A (TyEqSubstId Γ⊢A)
    Γ⊢id▶a≡id▶b⇒Γ▷A = sbEqExt₂ (SbId ⊢Γ) Γ⊢A Γ⊢a≡b∷Aid
    Γ⊢fa∷B[id▶a] = TmApp Γ⊢f∷PiAB Γ⊢a∷A
    Γ⊢gb∷B[id▶b] = TmApp Γ⊢g∷PiAB Γ⊢b∷A
    Γ⊢B[id▶a]≡B[id▶b] = tyEqSubst₂ Γ▷A⊢B Γ⊢id▶a≡id▶b⇒Γ▷A
    Γ⊢gb∷B[id▶a] = TmTyConv Γ⊢gb∷B[id▶b] (TyEqSym Γ⊢B[id▶a]≡B[id▶b])
  in Γ⊢fa∷B[id▶a] , Γ⊢gb∷B[id▶a]
...| TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢A = tmEqWfTy Δ⊢a≡b∷A
    Δ⊢a∷A , Δ⊢b∷A = tmEqWf Δ⊢a≡b∷A
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
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
    ctxExtInv Δ₁ B₁ Δ₁⊢B₁ ⊢Δ≡Δ₁▷B₁ , Γ⊢γ⇒Δ₁ , Γ⊢a∷B₁[γ] = sbExtInversion Γ⊢γ▶a⇒Δ
    varExist Δ₂ B₂ Δ₂⊢B₂ Δ⊢drop1⇒Δ₂ Δ⊢id⇒Δ₂▷B₂ , Δ⊢A≡B₂[drop1] = varTmInversion Δ⊢Var0∷A
    ⊢Δ≡Δ₂▷B₂ = idInversion Δ⊢id⇒Δ₂▷B₂
    ⊢Δ₁▷B₁≡Δ₂▷B₂ = ctxEqTrans (ctxEqSym ⊢Δ≡Δ₁▷B₁) ⊢Δ≡Δ₂▷B₂
    ⊢Δ₁≡Δ₂ , Δ₁⊢B₁≡B₂ = ctxEqExtInversion ⊢Δ₁▷B₁≡Δ₂▷B₂
    Γ⊢γ▶a⇒Δ₂▷B₂ = SbConv Γ⊢γ▶a⇒Δ ⊢Δ≡Δ₂▷B₂
    Δ₂▷B₂⊢drop⇒Δ₂ = display Δ₂⊢B₂
    Δ₂▷B₂⊢A≡B₂[drop1] = tyEqStability ⊢Δ≡Δ₂▷B₂ Δ⊢A≡B₂[drop1]
    open TyEqReason
    Γ⊢A[γ▶a]≡B₁[γ] = 
      Γ ⊢begin-ty
        A [ γ ▶ a ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ₂▷B₂⊢A≡B₂[drop1] Γ⊢γ▶a⇒Δ₂▷B₂ ⟩
        B₂ [ drop 1 ]ₑ [ γ ▶ a ]ₑ
      ty-≡⟨ TyEqSubstSubst Δ₂▷B₂⊢drop⇒Δ₂ Γ⊢γ▶a⇒Δ₂▷B₂ Δ₂⊢B₂ ⟩
        B₂ [ (drop 1) ∘ γ ▶ a ]ₑ
      ty-≡⟨ tyEqSubst₂ Δ₂⊢B₂ (SbEqDropExt Δ₂▷B₂⊢drop⇒Δ₂ Γ⊢γ▶a⇒Δ₂▷B₂) ⟩
        B₂ [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ₁⊢B₁≡B₂ Γ⊢γ⇒Δ₁ ⟨∣
        B₁ [ γ ]ₑ
      ∎
    Γ⊢a∷A[γ▶a] = TmTyConv Γ⊢a∷B₁[γ] (TyEqSym Γ⊢A[γ▶a]≡B₁[γ])
  in TmSubst Δ⊢Var0∷A Γ⊢γ▶a⇒Δ , Γ⊢a∷A[γ▶a]
...| TmEqSubstVarDrop Δ⊢VarX∷A Γ⊢dropY⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢VarX∷A
    Γ⊢VarX+Y∷A[dropY] = liftVar Δ⊢A Δ⊢VarX∷A Γ⊢dropY⇒Δ
  in TmSubst Δ⊢VarX∷A Γ⊢dropY⇒Δ , Γ⊢VarX+Y∷A[dropY]
...| TmEqLamSubst {Δ} {a} {A} {B} {Γ} {γ} Δ⊢Lam-a∷PiAB Γ⊢γ⇒Δ = let
    C , D , Δ⊢C , Δ▷C⊢D , Δ⊢PiAB≡PiCD , Δ▷C⊢a∷D = lamTmInversion Δ⊢Lam-a∷PiAB
    Γ⊢C[γ] = TySubst Δ⊢C Γ⊢γ⇒Δ
    Δ⊢PiCD = TyPi Δ⊢C Δ▷C⊢D
    Γ▷C[γ]⊢drop1⇒Γ = display Γ⊢C[γ]
    Γ▷C[γ]⊢liftγ⇒Δ▷C = liftSb Γ⊢γ⇒Δ Δ⊢C
    Γ▷C[γ]⊢a[liftγ]∷D[liftγ] = TmSubst Δ▷C⊢a∷D Γ▷C[γ]⊢liftγ⇒Δ▷C
    Γ⊢Lam-a[liftγ]∷PiC[γ][D[liftγ]] = TmLam Γ⊢C[γ] Γ▷C[γ]⊢a[liftγ]∷D[liftγ]
    open TyEqReason
    Γ⊢PiC[γ][D[liftγ]]≡PiAB[γ] = 
      Γ ⊢begin-ty
        Pi (C [ γ ]ₑ) (D [ lift γ ]ₑ)
      ty-≡⟨ TyEqPiSubst Δ⊢PiCD Γ⊢γ⇒Δ ⟨
        Pi C D [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ⊢PiAB≡PiCD Γ⊢γ⇒Δ ⟨∣
        Pi A B [ γ ]ₑ
      ∎
  in TmSubst Δ⊢Lam-a∷PiAB Γ⊢γ⇒Δ , TmTyConv Γ⊢Lam-a[liftγ]∷PiC[γ][D[liftγ]] Γ⊢PiC[γ][D[liftγ]]≡PiAB[γ]
...| TmEqPiSubst {Δ} {A} {B} {l} {Γ} {γ} Δ⊢PiAB∷Ul Γ⊢γ⇒Δ = let
    ⊢Δ = tmWfCtx Δ⊢PiAB∷Ul
    Γ⊢Ul[γ]≡Ul = TyEqUSubst (TyU ⊢Δ) Γ⊢γ⇒Δ
    Γ⊢PiAB[γ]∷Ul[γ] = TmSubst Δ⊢PiAB∷Ul Γ⊢γ⇒Δ
    (uLvlConjInv l' l₁ l₂ l₁⊔l₂≡l') , Δ⊢Ul≡Ul' , Δ⊢A∷Ul₁ , Δ▷A⊢B∷Ul₂ = piTmInversion Δ⊢PiAB∷Ul
    Δ⊢A = TyRussel Δ⊢A∷Ul₁
    ⊢Δ▷A = ctxExt Δ⊢A
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    ⊢Γ▷A[γ] = ctxExt Γ⊢A[γ]
    Γ▷A[γ]⊢liftγ⇒Δ▷A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ⊢A[γ]∷Ul₁ = (TmTyConv (TmSubst Δ⊢A∷Ul₁ Γ⊢γ⇒Δ) (TyEqUSubst (TyU ⊢Δ) Γ⊢γ⇒Δ)) 
    Γ▷A[γ]⊢B[liftγ]∷Ul₂ = (TmTyConv (TmSubst Δ▷A⊢B∷Ul₂ Γ▷A[γ]⊢liftγ⇒Δ▷A) (TyEqUSubst (TyU ⊢Δ▷A) Γ▷A[γ]⊢liftγ⇒Δ▷A)) 
    Γ⊢PiA[γ]B[liftγ]∷Ul₁⊔l₂ = TmPi Γ⊢A[γ]∷Ul₁ Γ▷A[γ]⊢B[liftγ]∷Ul₂
    Γ⊢Ul₁⊔l₂≡Ul' = tyUnivCong (sbWfCtx Γ⊢γ⇒Δ) l₁⊔l₂≡l'
    open TyEqReason
    Γ⊢Ul≡Ul₁⊔l₂ =  
      Γ ⊢begin-ty
        U l
      ty-≡⟨ TyEqUSubst (TyU ⊢Δ) Γ⊢γ⇒Δ ⟨  
        U l [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ⊢Ul≡Ul' Γ⊢γ⇒Δ ⟩
        U l' [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ (tyUnivCong ⊢Δ l₁⊔l₂≡l') Γ⊢γ⇒Δ ⟨
        U (l₁ ⊔ l₂) [ γ ]ₑ
      ty-≡⟨ TyEqUSubst (TyU ⊢Δ) Γ⊢γ⇒Δ ⟩∣
        U (l₁ ⊔ l₂)
      ∎
  in TmTyConv Γ⊢PiAB[γ]∷Ul[γ] Γ⊢Ul[γ]≡Ul , tmTyConv' Γ⊢PiA[γ]B[liftγ]∷Ul₁⊔l₂ Γ⊢Ul≡Ul₁⊔l₂
...| TmEqAppSubst {Δ} {f} {a} {T} {Γ} {γ} Δ⊢f∙a∷T Γ⊢γ⇒Δ = let
    A , B , Δ⊢PiAB , Δ⊢f∷PiAB , Δ⊢a∷A , Δ⊢T≡B[id▶a] = appTmInversion Δ⊢f∙a∷T
    Δ⊢A , Δ▷A⊢B = piTyInversion Δ⊢PiAB
    ⊢Δ = tyWfCtx Δ⊢A
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ⊢a[γ]∷A[γ] = TmSubst Δ⊢a∷A Γ⊢γ⇒Δ
    Δ⊢id▶a⇒Δ▷A = section Δ⊢A Δ⊢a∷A
    Γ⊢id▶a[γ]⇒Γ▷A[γ] = section Γ⊢A[γ] Γ⊢a[γ]∷A[γ]
    Γ▷A[γ]⊢liftγ⇒Δ▷A = liftSb Γ⊢γ⇒Δ Δ⊢A
    open TyEqReason
    Γ⊢liftγ∘id▶a[γ]≡id▶a∘γ⇒Δ▷A = liftSectionCommute Γ⊢γ⇒Δ Δ⊢A Δ⊢a∷A
    Γ⊢B[liftγ][id▶a]≡T[γ] = 
      Γ ⊢begin-ty
        B [ lift γ ]ₑ [ idₛ ▶ a [ γ ]ₑ ]ₑ
      ty-≡⟨ TyEqSubstSubst Γ▷A[γ]⊢liftγ⇒Δ▷A Γ⊢id▶a[γ]⇒Γ▷A[γ] Δ▷A⊢B ⟩
        B [ lift γ ∘ idₛ ▶ a [ γ ]ₑ ]ₑ
      ty-≡⟨ tyEqSubst₂ Δ▷A⊢B Γ⊢liftγ∘id▶a[γ]≡id▶a∘γ⇒Δ▷A ⟩
        B [ idₛ ▶ a ∘ γ ]ₑ
      ty-≡⟨ TyEqSubstSubst Δ⊢id▶a⇒Δ▷A Γ⊢γ⇒Δ Δ▷A⊢B ⟨
        B [ idₛ ▶ a ]ₑ [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ⊢T≡B[id▶a] Γ⊢γ⇒Δ ⟨∣
        T [ γ ]ₑ
      ∎
      
    Γ⊢f[γ]∙a[γ]∷T[γ] =
      begin
        intro-⟨ Δ⊢f∷PiAB ⟩ Δ ⊢ f ∷ Pi A B 
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢γ⇒Δ ⟩
        Γ ⊢ f [ γ ]ₑ ∷ Pi A B [ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ) ⟩
        Γ ⊢ f [ γ ]ₑ ∷ Pi (A [ γ ]ₑ) (B [ lift γ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-App-on  Γ⊢a[γ]∷A[γ] ⟩
        Γ ⊢ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ B [ lift γ ]ₑ [ idₛ ▶ a [ γ ]ₑ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by Γ⊢B[liftγ][id▶a]≡T[γ] ⟩
        Γ ⊢ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ T [ γ ]ₑ
      ∎
  in (TmSubst Δ⊢f∙a∷T Γ⊢γ⇒Δ) , Γ⊢f[γ]∙a[γ]∷T[γ]
...| TmEqSubstSubst {Δ} {δ} {Ξ} {Γ} {γ} {a} {A} Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A = let
    Ξ⊢A = tmWfTy Ξ⊢a∷A
    Γ⊢a[δ∘γ]∷A[δ][γ] = 
      begin
        (intro-⟨ Δ⊢δ⇒Ξ ⟩ Δ ⊢ δ ⇒ Ξ) , (intro-⟨ Γ⊢γ⇒Δ ⟩ Γ ⊢ γ ⇒ Δ)
      ⎯⎯⎯⎯⟨ Sb-Comp ⟩
        Γ ⊢ δ ∘ γ ⇒ Ξ
      ⎯⎯⎯⎯⟨ Tm-Subst-on Ξ⊢a∷A ⟩
        Γ ⊢ a [ δ ∘ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A) ⟩
        Γ ⊢ a [ δ ∘ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ
      ∎
  in TmSubst (TmSubst Ξ⊢a∷A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ , Γ⊢a[δ∘γ]∷A[δ][γ]
...| TmEqUSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Γ⊢Ul∷USl[γ] = TmSubst (TmU ⊢Δ) Γ⊢γ⇒Δ
  in TmTyConv Γ⊢Ul∷USl[γ] (TyEqUSubst (TyU ⊢Δ) Γ⊢γ⇒Δ) , TmU ⊢Γ
...| TmEqPiBeta Γ⊢A Γ▷A⊢b∷B Γ⊢a∷A = let
    Γ⊢Lam-b∷PiAB = TmLam Γ⊢A Γ▷A⊢b∷B
    Γ⊢id▶a⇒Γ▷A = section Γ⊢A Γ⊢a∷A
  in TmApp Γ⊢Lam-b∷PiAB Γ⊢a∷A , TmSubst Γ▷A⊢b∷B Γ⊢id▶a⇒Γ▷A
...| TmEqPiEta {Γ} {f} {A} {B} Γ⊢f∷PiAB = let
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
    Γ⊢A , Γ▷A⊢B = piTyInversion Γ⊢PiAB
    ⊢Γ▷A = ctxExt Γ⊢A
    Γ▷A⊢drop1⇒Γ = display Γ⊢A
    Γ▷A⊢A[drop1] = TySubst Γ⊢A Γ▷A⊢drop1⇒Γ
    Γ▷A⊢var0∷A[drop1] = TmVarᶻ Γ⊢A
    Γ▷A⊢id▶var0⇒Γ▷A▷A[drop1] = section Γ▷A⊢A[drop1] Γ▷A⊢var0∷A[drop1]
    Γ▷A▷A[drop1]⊢lift[drop1]⇒Γ▷A = liftSb Γ▷A⊢drop1⇒Γ Γ⊢A
    open TyEqReason
    tyEq = 
      Γ ▷ A ⊢begin-ty
        B [ lift (drop 1) ]ₑ [ idₛ ▶ Var 0 ]ₑ
      ty-≡⟨ TyEqSubstSubst Γ▷A▷A[drop1]⊢lift[drop1]⇒Γ▷A Γ▷A⊢id▶var0⇒Γ▷A▷A[drop1] Γ▷A⊢B ⟩
        B [ lift (drop 1) ∘ idₛ ▶ Var 0 ]ₑ
      ty-≡⟨ tyEqSubst₂ Γ▷A⊢B (liftDropEq Γ⊢A) ⟩
        B [ idₛ ]ₑ
      ty-≡⟨ TyEqSubstId Γ▷A⊢B ⟩∣
        B
      ∎

    Γ⊢Lam[f[drop1]∙Var0]∷PiAB = 
      begin
        intro-⟨ Γ⊢f∷PiAB ⟩ Γ ⊢ f ∷ Pi A B
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ▷A⊢drop1⇒Γ ⟩
        Γ ▷ A ⊢ f [ drop 1 ]ₑ ∷ Pi A B [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqPiSubst Γ⊢PiAB Γ▷A⊢drop1⇒Γ) ⟩
        Γ ▷ A ⊢ f [ drop 1 ]ₑ ∷ Pi (A [ drop 1 ]ₑ) (B [ lift (drop 1) ]ₑ) 
      ⎯⎯⎯⎯⟨ Tm-App-on Γ▷A⊢var0∷A[drop1] ⟩
        Γ ▷ A ⊢ (f [ drop 1 ]ₑ) ∙ Var 0 ∷ B [ lift (drop 1) ]ₑ [ idₛ ▶ Var 0 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by tyEq ⟩
        Γ ▷ A ⊢ (f [ drop 1 ]ₑ) ∙ Var 0 ∷ B
      ⎯⎯⎯⎯⟨ Tm-Lam-abs Γ⊢A ⟩
        Γ ⊢ Lam ((f [ drop 1 ]ₑ) ∙ Var 0) ∷ Pi A B
      ∎
  in Γ⊢f∷PiAB , Γ⊢Lam[f[drop1]∙Var0]∷PiAB
