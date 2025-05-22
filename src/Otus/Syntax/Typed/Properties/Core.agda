{-# OPTIONS --without-K  --safe #-}
module Otus.Syntax.Typed.Properties.Core where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Reason
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Heter
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
    (Γ ◁ A ⊢ B) ×
    (Γ ⊢ T ≡ⱼ Pi A B) ×
    (Γ ◁ A ⊢ a ∷ B)
lamTmInversion (TmLam Γ⊢A Γ◁A⊢a∷B) = let
    Γ◁A⊢B = tmWfTy Γ◁A⊢a∷B
    Γ⊢PiAB = TyPi Γ⊢A Γ◁A⊢B
  in _ , _ , Γ⊢A , Γ◁A⊢B , TyEqRefl Γ⊢PiAB , Γ◁A⊢a∷B
lamTmInversion (TmTyConv Γ⊢Lam-a∷G Γ⊢G≡T) = let
    _ , _ , Γ⊢A , Γ◁A⊢B , Γ⊢G≡PiAB , Γ◁A⊢b∷B = lamTmInversion Γ⊢Lam-a∷G
  in _ , _ , Γ⊢A , Γ◁A⊢B , (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡PiAB) , Γ◁A⊢b∷B

appTmInversion : Γ ⊢ f ∙ a ∷ T
  → Σ[ A ∈ Term ] Σ[ B ∈ Term ]
    (Γ ⊢ Pi A B) × 
    (Γ ⊢ f ∷ Pi A B) ×
    (Γ ⊢ a ∷ A) ×
    (Γ ⊢ T ≡ⱼ B [ idₛ ◀ a ]ₑ)
appTmInversion Γ⊢f∙a∷T@(TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
  in _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , (TyEqRefl (tmWfTy Γ⊢f∙a∷T))
appTmInversion (TmTyConv Γ⊢f∙a∷G Γ⊢G≡T) = let
    _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , Γ⊢G≡B[id◀a] = appTmInversion Γ⊢f∙a∷G
  in _ , _ , Γ⊢PiAB , Γ⊢f∷PiAB , Γ⊢a∷A , TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡B[id◀a]

-- tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmWfTy tm with tm
...| TmVarᶻ Γ⊢A = let 
    Γ◁A⊢drop1⇒Γ = display Γ⊢A
  in TySubst Γ⊢A Γ◁A⊢drop1⇒Γ
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = let 
    Γ⊢A = tmWfTy Γ⊢VarX∷A
    Γ◁B⊢drop1⇒Γ = display Γ⊢B
  in TySubst Γ⊢A Γ◁B⊢drop1⇒Γ
...| TmPi Γ⊢A∷U Γ◁A⊢B∷U = TyUniv (tmWfCtx Γ⊢A∷U)
...| TmLam Γ⊢A Γ◁A⊢b∷B = TyPi Γ⊢A (tmWfTy Γ◁A⊢b∷B)
...| TmApp Γ⊢f∷PiAB Γ⊢a∷A = let 
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
    Γ⊢A , Γ◁A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢id◀a⇒Γ◁A = section Γ⊢A Γ⊢a∷A
  in TySubst Γ◁A⊢B Γ⊢id◀a⇒Γ◁A
...| TmNat ⊢Γ = TyUniv ⊢Γ
...| TmZero ⊢Γ = TyNat ⊢Γ
...| TmSucc Γ⊢a∷Nat = tmWfTy Γ⊢a∷Nat
...| TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢A[drop2◀SVar1] Γ⊢c∷ℕ = let
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    Γ⊢id◀c⇒Γ◁ℕ = section (TyNat ⊢Γ) (Γ⊢c∷ℕ)
  in TySubst Γ◁ℕ⊢A Γ⊢id◀c⇒Γ◁ℕ
...| TmSubst Δ⊢a∷A Γ⇒Δ = let 
    Δ⊢A = tmWfTy Δ⊢a∷A
  in TySubst Δ⊢A Γ⇒Δ
...| TmUniv ⊢Γ = TyUniv ⊢Γ
...| TmTyConv _ Γ⊢A≡B = proj₂ (tyEqWf Γ⊢A≡B)




-- tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
tyEqWf eq with eq
...| TyEqRefl Γ⊢A = Γ⊢A , Γ⊢A
...| TyEqSym Γ⊢B≡A = swap (tyEqWf Γ⊢B≡A)
...| TyEqTrans Γ⊢A≡B Γ⊢B≡C = proj₁₂ (tyEqWf Γ⊢A≡B) (tyEqWf Γ⊢B≡C)
...| TyEqPi Γ⊢A Γ⊢A≡B Γ◁A⊢C≡D = let 
    Γ⊢B = proj₂ (tyEqWf Γ⊢A≡B)
    Γ◁A⊢C , Γ◁A⊢D = tyEqWf Γ◁A⊢C≡D
    ⊢Γ = tyWfCtx Γ⊢A
    ⊢Γ◁A≡Γ◁B = ctxEqExt₂ ⊢Γ Γ⊢A Γ⊢B Γ⊢A≡B
    Γ◁B⊢D = tyStability ⊢Γ◁A≡Γ◁B Γ◁A⊢D
  in TyPi Γ⊢A Γ◁A⊢C , TyPi Γ⊢B Γ◁B⊢D
...| TyEqSubst Δ⊢A≡B Γ⊢γ₁≡γ₂⇒Δ = let 
    Δ⊢A , Δ⊢B = tyEqWf Δ⊢A≡B
    Γ⊢γ₁⇒Δ , Γ⊢γ₂⇒Δ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
  in TySubst Δ⊢A Γ⊢γ₁⇒Δ , TySubst Δ⊢B Γ⊢γ₂⇒Δ
...| TyEqRussel Γ⊢A≡B∷U = let 
    Γ⊢A∷U , Γ⊢B∷U = tmEqWf Γ⊢A≡B∷U
  in TyRussel Γ⊢A∷U , TyRussel Γ⊢B∷U
...| TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ = let 
    Δ⊢A , Δ◁A⊢B = piTyInversion Δ⊢PiAB
    Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ◁Aγ⊢↑γ⇒Δ◁A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ◁Aγ⊢B[↑γ] = TySubst Δ◁A⊢B Γ◁Aγ⊢↑γ⇒Δ◁A
  in TySubst Δ⊢PiAB Γ⊢γ⇒Δ , TyPi Γ⊢Aγ Γ◁Aγ⊢B[↑γ]
...| TyEqNatSubst Γ⊢γ⇒Δ = let 
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
  in TySubst (TyNat ⊢Δ) Γ⊢γ⇒Δ , TyNat ⊢Γ
...| TyEqUSubst Γ⊢γ⇒Δ = let 
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
  in TySubst (TyUniv ⊢Δ) Γ⊢γ⇒Δ , TyUniv ⊢Γ
...| TyEqSubstSubst Ξ⊢A Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let 
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
...| TmEqLam Γ⊢A Γ◁A⊢a≡b∷B = let 
    Γ◁A⊢B = tmEqWfTy Γ◁A⊢a≡b∷B
  in TyPi Γ⊢A Γ◁A⊢B
...| TmEqPi Γ⊢A _ _ = TyUniv (tyWfCtx Γ⊢A)
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    Γ⊢A , Γ◁A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢id◀a⇒Γ◁A = section Γ⊢A (proj₁ (tmEqWf Γ⊢a≡b∷A))
  in TySubst Γ◁A⊢B Γ⊢id◀a⇒Γ◁A
...| TmEqSucc Γ⊢a≡b∷Nat = let
    ⊢Γ = tmEqWfCtx Γ⊢a≡b∷Nat
  in TyNat ⊢Γ
...| TmEqNatElim Γ◁ℕ⊢A₁ Γ◁ℕ⊢A₁≡A₂ Γ⊢a₁≡a₂∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Γ⊢c₁≡c₂∷Nat = let
    ⊢Γ = tmEqWfCtx Γ⊢c₁≡c₂∷Nat
    Γ◁ℕ⊢A₁ = proj₁ (tyEqWf Γ◁ℕ⊢A₁≡A₂)
    Γ⊢id◀c₁⇒Γ◁ℕ = section (TyNat ⊢Γ) (proj₁ (tmEqWf Γ⊢c₁≡c₂∷Nat))
  in TySubst Γ◁ℕ⊢A₁ Γ⊢id◀c₁⇒Γ◁ℕ
...| TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ = let
    Δ⊢A = tmEqWfTy Δ⊢a≡b∷A
    Γ⊢γ₁⇒Δ , _ = sbEqWf Γ⊢γ₁≡γ₂⇒Δ
  in TySubst Δ⊢A Γ⊢γ₁⇒Δ
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let
    _ , Γ⊢B = tyEqWf Γ⊢A≡B
  in Γ⊢B
...| TmEqSubstId Γ⊢a∷A = tmWfTy Γ⊢a∷A
...| TmEqSubstVarExt Δ⊢Var0∷A Γ⊢γ◀a⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢Var0∷A
  in TySubst Δ⊢A Γ⊢γ◀a⇒Δ
...| TmEqSubstVarDrop Δ⊢VarX∷A Γ⊢dropY⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢VarX∷A
  in TySubst Δ⊢A Γ⊢dropY⇒Δ
...| TmEqLamSubst Δ⊢LamA∷PiAB Γ⊢γ⇒Δ = let
    Δ⊢PiAB = tmWfTy Δ⊢LamA∷PiAB
  in TySubst Δ⊢PiAB Γ⊢γ⇒Δ
...| TmEqPiSubst Δ⊢PiAB∷Ul Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyUniv ⊢Γ
...| TmEqAppSubst Δ⊢f∙a∷A Γ⊢γ⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢f∙a∷A
  in TySubst Δ⊢A Γ⊢γ⇒Δ
...| TmEqNatSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyUniv ⊢Γ
...| TmEqZeroSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyNat ⊢Γ
...| TmEqSuccSubst _ Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyNat ⊢Γ
...| TmEqNatElimSubst Δ⊢NatElim∷A[id◀c] Γ⊢γ⇒Δ = let 
    Δ⊢A[id◀c] = tmWfTy Δ⊢NatElim∷A[id◀c]
  in TySubst Δ⊢A[id◀c] Γ⊢γ⇒Δ
...| TmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A = let
    Ξ⊢A = tmWfTy Ξ⊢a∷A
  in TySubst (TySubst Ξ⊢A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
...| TmEqUSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
  in TyUniv ⊢Γ
...| TmEqPiBeta Γ⊢A Γ◁A⊢b∷B Γ⊢a∷A = let
    Γ◁A⊢B = tmWfTy Γ◁A⊢b∷B
    Γ⊢id◀a⇒Γ◁A = section Γ⊢A Γ⊢a∷A
  in TySubst Γ◁A⊢B Γ⊢id◀a⇒Γ◁A
...| TmEqNatElimZero Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmWfTy Γ⊢a∷A[id◀Z]
...| TmEqNatElimSucc Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢A[drop2◀SVar1] Γ⊢c∷ℕ = let
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    Γ⊢id◀sc⇒Γ◁ℕ = section (TyNat ⊢Γ) (TmSucc Γ⊢c∷ℕ)
  in TySubst Γ◁ℕ⊢A Γ⊢id◀sc⇒Γ◁ℕ
...| TmEqPiEta Γ⊢f∷PiAB = tmWfTy Γ⊢f∷PiAB
...| TmEqNatEta Γ⊢c∷ℕ = tmWfTy Γ⊢c∷ℕ

-- tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A
tmEqWf eq with eq
...| TmEqRefl Γ⊢a∷A = Γ⊢a∷A , Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = swap (tmEqWf Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = proj₁₂ (tmEqWf Γ⊢a≡b∷A) (tmEqWf Γ⊢b≡c∷A)
...| TmEqLam Γ⊢A Γ◁A⊢a≡b∷B = let 
    Γ◁A⊢a∷B , Γ◁A⊢b∷B = tmEqWf Γ◁A⊢a≡b∷B
  in TmLam Γ⊢A Γ◁A⊢a∷B , TmLam Γ⊢A Γ◁A⊢b∷B
...| TmEqPi Γ⊢A Γ⊢A≡B∷Ul₁ Γ◁A⊢C≡D∷Ul₂ = let 
    Γ⊢A∷Ul₁ , Γ⊢B∷Ul₁ = tmEqWf Γ⊢A≡B∷Ul₁
    Γ◁A⊢C∷Ul₂ , Γ◁A⊢D∷Ul₂ = tmEqWf Γ◁A⊢C≡D∷Ul₂
    Γ⊢A≡B = TyEqRussel Γ⊢A≡B∷Ul₁
    ⊢Γ = tyWfCtx Γ⊢A
    ⊢Γ◁A≡Γ◁B = ctxEqExt₂ ⊢Γ (TyRussel Γ⊢A∷Ul₁) (TyRussel Γ⊢B∷Ul₁) Γ⊢A≡B
    Γ◁B⊢D∷Ul₂ = tmStability ⊢Γ◁A≡Γ◁B Γ◁A⊢D∷Ul₂
  in TmPi Γ⊢A∷Ul₁ Γ◁A⊢C∷Ul₂ , TmPi Γ⊢B∷Ul₁ Γ◁B⊢D∷Ul₂
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    ⊢Γ = tmEqWfCtx Γ⊢f≡g∷PiAB
    Γ⊢f∷PiAB , Γ⊢g∷PiAB = tmEqWf Γ⊢f≡g∷PiAB
    Γ⊢a∷A , Γ⊢b∷A = tmEqWf Γ⊢a≡b∷A
    Γ⊢A , Γ◁A⊢B = piTyInversion Γ⊢PiAB
    Γ⊢a≡b∷Aid = tmEqConv' Γ⊢a≡b∷A (TyEqSubstId Γ⊢A)
    Γ⊢id◀a≡id◀b⇒Γ◁A = sbEqExt₂ (SbId ⊢Γ) Γ⊢A Γ⊢a≡b∷Aid
    Γ⊢fa∷B[id◀a] = TmApp Γ⊢f∷PiAB Γ⊢a∷A
    Γ⊢gb∷B[id◀b] = TmApp Γ⊢g∷PiAB Γ⊢b∷A
    Γ⊢B[id◀a]≡B[id◀b] = tyEqSubst₂ Γ◁A⊢B Γ⊢id◀a≡id◀b⇒Γ◁A
    Γ⊢gb∷B[id◀a] = TmTyConv Γ⊢gb∷B[id◀b] (TyEqSym Γ⊢B[id◀a]≡B[id◀b])
  in Γ⊢fa∷B[id◀a] , Γ⊢gb∷B[id◀a]
...| TmEqSucc Γ⊢a≡b∷Nat = let
    Γ⊢a∷Nat , Γ⊢b∷Nat = tmEqWf Γ⊢a≡b∷Nat
  in TmSucc Γ⊢a∷Nat , TmSucc Γ⊢b∷Nat
...| TmEqNatElim {Γ} {A₁} {A₂} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} Γ◁ℕ⊢A₁ Γ◁ℕ⊢A₁≡A₂ Γ⊢a₁≡a₂∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Γ⊢c₁≡c₂∷Nat = let
    ⊢Γ = tmEqWfCtx Γ⊢c₁≡c₂∷Nat
    ⊢Γ◁ℕ = tyEqWfCtx Γ◁ℕ⊢A₁≡A₂
    Γ⊢ℕ =  TyNat ⊢Γ
    Γ◁ℕ⊢A₁ , Γ◁ℕ⊢A₂ = tyEqWf Γ◁ℕ⊢A₁≡A₂
    Γ⊢a₁∷A₁[id◀Z] , Γ⊢a₂∷A₁[id◀Z] = tmEqWf Γ⊢a₁≡a₂∷A₁[id◀Z]
    Γ◁ℕ◁A₁⊢b₁∷A₁[drop2◀SVar1] , Γ◁ℕ◁A₁⊢b₂∷A₁[drop2◀SVar1] = tmEqWf Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1]
    Γ⊢c₁∷Nat , Γ⊢c₂∷Nat = tmEqWf Γ⊢c₁≡c₂∷Nat
    Γ⊢id◀c₁≡id◀c₂⇒Γ◁ℕ = sectionEq Γ⊢ℕ Γ⊢c₁≡c₂∷Nat
    ⊢Γ◁ℕ◁A₁≡Γ◁ℕ◁A₂ = ctxEqExt₂ ⊢Γ◁ℕ Γ◁ℕ⊢A₁ Γ◁ℕ⊢A₂ Γ◁ℕ⊢A₁≡A₂
    Γ⊢A₁[id◀c₁]≡A₂[id◀c₂] = TyEqSubst Γ◁ℕ⊢A₁≡A₂ Γ⊢id◀c₁≡id◀c₂⇒Γ◁ℕ
    Γ◁ℕ◁A₁⊢drop2⇒Γ = SbDropˢ (SbDropˢ (SbId ⊢Γ) Γ⊢ℕ) Γ◁ℕ⊢A₁
    Γ⊢a₂∷A₂[id◀Z] =
      begin
      intro-⟨ section Γ⊢ℕ (TmZero ⊢Γ) ⟩
        (Γ ⊢ idₛ ◀ Zero ⇒ Γ ◁ Nat)
      ⎯⎯⎯⎯⟨ tyEqSubst₁ Γ◁ℕ⊢A₁≡A₂ ⟩
        Γ ⊢ A₁ [ idₛ ◀ Zero ]ₑ ≡ⱼ A₂ [ idₛ ◀ Zero ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-on Γ⊢a₂∷A₁[id◀Z] ⟩
        (Γ ⊢ a₂ ∷ A₂ [ idₛ ◀ Zero ]ₑ)
      ∎
    Γ◁ℕ◁A₂⊢b₂∷A₂[drop2◀SVar1] = 
      begin
      intro-⟨ Γ⊢ℕ ⟩ 
        (Γ ⊢ Nat)
      ⎯⎯⎯⎯⟨ Tm-Varᶻ ⟩
        Γ ◁ Nat ⊢ Var 0 ∷ Nat [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqNatSubst (display Γ⊢ℕ)) ⟩
        Γ ◁ Nat ⊢ Var 0 ∷ Nat
      ⎯⎯⎯⎯⟨ Tm-Var-ext Γ◁ℕ⊢A₁ ⟩
        Γ ◁ Nat ◁ A₁ ⊢ Var 1 ∷ Nat [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqNatSubst (display Γ◁ℕ⊢A₁)) ⟩
        Γ ◁ Nat ◁ A₁ ⊢ Var 1 ∷ Nat
      ⎯⎯⎯⎯⟨ TmSucc ⟩
        Γ ◁ Nat ◁ A₁ ⊢ Succ (Var 1) ∷ Nat
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqNatSubst Γ◁ℕ◁A₁⊢drop2⇒Γ) ⟩
        Γ ◁ Nat ◁ A₁ ⊢ Succ (Var 1) ∷ Nat [ drop 2 ]ₑ
      ⎯⎯⎯⎯⟨ Sb-Ext-to Γ◁ℕ◁A₁⊢drop2⇒Γ Γ⊢ℕ ⟩
        Γ ◁ Nat ◁ A₁ ⊢ drop 2 ◀ Succ (Var 1) ⇒ Γ ◁ Nat
      ⎯⎯⎯⎯⟨ tyEqSubst₁ Γ◁ℕ⊢A₁≡A₂ ⟩
        Γ ◁ Nat ◁ A₁ ⊢ A₁ [ drop 2 ◀ Succ (Var 1) ]ₑ ≡ⱼ A₂ [ drop 2 ◀ Succ (Var 1) ]ₑ
      ⎯⎯⎯⎯⟨ tmTyConv Γ◁ℕ◁A₁⊢b₂∷A₁[drop2◀SVar1] ⟩
        (Γ ◁ Nat ◁ A₁ ⊢ b₂ ∷ (A₂ [ drop 2 ◀ Succ (Var 1) ]ₑ))
      ⎯⎯⎯⎯⟨ tmStability ⊢Γ◁ℕ◁A₁≡Γ◁ℕ◁A₂ ⟩
        (Γ ◁ Nat ◁ A₂ ⊢ b₂ ∷ A₂ [ drop 2 ◀ Succ (Var 1) ]ₑ)
      ∎
    Γ⊢NatElim₂∷A₂[id◀c₂] = TmNatElim Γ◁ℕ⊢A₂ Γ⊢a₂∷A₂[id◀Z] Γ◁ℕ◁A₂⊢b₂∷A₂[drop2◀SVar1] Γ⊢c₂∷Nat
  in TmNatElim Γ◁ℕ⊢A₁ Γ⊢a₁∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁∷A₁[drop2◀SVar1] Γ⊢c₁∷Nat , 
    TmTyConv Γ⊢NatElim₂∷A₂[id◀c₂] (TyEqSym  Γ⊢A₁[id◀c₁]≡A₂[id◀c₂])
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
...| TmEqSubstVarExt {Δ} {A} {Γ} {γ} {a} Δ⊢Var0∷A Γ⊢γ◀a⇒Δ = let 
    ctxExtInv Δ₁ B₁ Δ₁⊢B₁ ⊢Δ≡Δ₁◁B₁ , Γ⊢γ⇒Δ₁ , Γ⊢a∷B₁[γ] = sbExtInversion Γ⊢γ◀a⇒Δ
    varExist Δ₂ B₂ Δ₂⊢B₂ Δ⊢drop1⇒Δ₂ Δ⊢id⇒Δ₂◁B₂ , Δ⊢A≡B₂[drop1] = varTmInversion Δ⊢Var0∷A
    ⊢Δ≡Δ₂◁B₂ = idInversion Δ⊢id⇒Δ₂◁B₂
    ⊢Δ₁◁B₁≡Δ₂◁B₂ = ctxEqTrans (ctxEqSym ⊢Δ≡Δ₁◁B₁) ⊢Δ≡Δ₂◁B₂
    ⊢Δ₁≡Δ₂ , Δ₁⊢B₁≡B₂ = ctxEqExtInversion ⊢Δ₁◁B₁≡Δ₂◁B₂
    Γ⊢γ◀a⇒Δ₂◁B₂ = SbConv Γ⊢γ◀a⇒Δ ⊢Δ≡Δ₂◁B₂
    Δ₂◁B₂⊢drop⇒Δ₂ = display Δ₂⊢B₂
    Δ₂◁B₂⊢A≡B₂[drop1] = tyEqStability ⊢Δ≡Δ₂◁B₂ Δ⊢A≡B₂[drop1]
    open TyEqReason
    Γ⊢A[γ◀a]≡B₁[γ] = 
      Γ ⊢begin-ty
        A [ γ ◀ a ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ₂◁B₂⊢A≡B₂[drop1] Γ⊢γ◀a⇒Δ₂◁B₂ ⟩
        B₂ [ drop 1 ]ₑ [ γ ◀ a ]ₑ
      ty-≡⟨ TyEqSubstSubst Δ₂⊢B₂ Δ₂◁B₂⊢drop⇒Δ₂ Γ⊢γ◀a⇒Δ₂◁B₂ ⟩
        B₂ [ (drop 1) ∘ γ ◀ a ]ₑ
      ty-≡⟨ tyEqSubst₂ Δ₂⊢B₂ (SbEqDropExt Δ₂◁B₂⊢drop⇒Δ₂ Γ⊢γ◀a⇒Δ₂◁B₂) ⟩
        B₂ [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ₁⊢B₁≡B₂ Γ⊢γ⇒Δ₁ ⟨∣
        B₁ [ γ ]ₑ
      ∎
    Γ⊢a∷A[γ◀a] = TmTyConv Γ⊢a∷B₁[γ] (TyEqSym Γ⊢A[γ◀a]≡B₁[γ])
  in TmSubst Δ⊢Var0∷A Γ⊢γ◀a⇒Δ , Γ⊢a∷A[γ◀a]
...| TmEqSubstVarDrop Δ⊢VarX∷A Γ⊢dropY⇒Δ = let
    Δ⊢A = tmWfTy Δ⊢VarX∷A
    Γ⊢VarX+Y∷A[dropY] = liftVar Δ⊢A Δ⊢VarX∷A Γ⊢dropY⇒Δ
  in TmSubst Δ⊢VarX∷A Γ⊢dropY⇒Δ , Γ⊢VarX+Y∷A[dropY]
...| TmEqLamSubst {Δ} {a} {A} {B} {Γ} {γ} Δ⊢Lam-a∷PiAB Γ⊢γ⇒Δ = let
    C , D , Δ⊢C , Δ◁C⊢D , Δ⊢PiAB≡PiCD , Δ◁C⊢a∷D = lamTmInversion Δ⊢Lam-a∷PiAB
    Γ⊢C[γ] = TySubst Δ⊢C Γ⊢γ⇒Δ
    Δ⊢PiCD = TyPi Δ⊢C Δ◁C⊢D
    Γ◁C[γ]⊢drop1⇒Γ = display Γ⊢C[γ]
    Γ◁C[γ]⊢liftγ⇒Δ◁C = liftSb Γ⊢γ⇒Δ Δ⊢C
    Γ◁C[γ]⊢a[liftγ]∷D[liftγ] = TmSubst Δ◁C⊢a∷D Γ◁C[γ]⊢liftγ⇒Δ◁C
    Γ⊢Lam-a[liftγ]∷PiC[γ][D[liftγ]] = TmLam Γ⊢C[γ] Γ◁C[γ]⊢a[liftγ]∷D[liftγ]
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
    Γ⊢Ul[γ]≡Ul = TyEqUSubst Γ⊢γ⇒Δ
    Γ⊢PiAB[γ]∷Ul[γ] = TmSubst Δ⊢PiAB∷Ul Γ⊢γ⇒Δ
    (uLvlConjInv l' l₁ l₂ l₁⊔l₂≡l') , Δ⊢Ul≡Ul' , Δ⊢A∷Ul₁ , Δ◁A⊢B∷Ul₂ = piTmInversion Δ⊢PiAB∷Ul
    Δ⊢A = TyRussel Δ⊢A∷Ul₁
    ⊢Δ◁A = ctxExt Δ⊢A
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    ⊢Γ◁A[γ] = ctxExt Γ⊢A[γ]
    Γ◁A[γ]⊢liftγ⇒Δ◁A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ⊢A[γ]∷Ul₁ = (TmTyConv (TmSubst Δ⊢A∷Ul₁ Γ⊢γ⇒Δ) (TyEqUSubst Γ⊢γ⇒Δ)) 
    Γ◁A[γ]⊢B[liftγ]∷Ul₂ = (TmTyConv (TmSubst Δ◁A⊢B∷Ul₂ Γ◁A[γ]⊢liftγ⇒Δ◁A) (TyEqUSubst Γ◁A[γ]⊢liftγ⇒Δ◁A)) 
    Γ⊢PiA[γ]B[liftγ]∷Ul₁⊔l₂ = TmPi Γ⊢A[γ]∷Ul₁ Γ◁A[γ]⊢B[liftγ]∷Ul₂
    Γ⊢Ul₁⊔l₂≡Ul' = tyUnivCong (sbWfCtx Γ⊢γ⇒Δ) l₁⊔l₂≡l'
    open TyEqReason
    Γ⊢Ul≡Ul₁⊔l₂ =  
      Γ ⊢begin-ty
        Univ l
      ty-≡⟨ TyEqUSubst Γ⊢γ⇒Δ ⟨  
        Univ l [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ⊢Ul≡Ul' Γ⊢γ⇒Δ ⟩
        Univ l' [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ (tyUnivCong ⊢Δ l₁⊔l₂≡l') Γ⊢γ⇒Δ ⟨
        Univ (l₁ ⊔ l₂) [ γ ]ₑ
      ty-≡⟨ TyEqUSubst Γ⊢γ⇒Δ ⟩∣
        Univ (l₁ ⊔ l₂)
      ∎
  in TmTyConv Γ⊢PiAB[γ]∷Ul[γ] Γ⊢Ul[γ]≡Ul , tmTyConv' Γ⊢PiA[γ]B[liftγ]∷Ul₁⊔l₂ Γ⊢Ul≡Ul₁⊔l₂
...| TmEqAppSubst {Δ} {f} {a} {T} {Γ} {γ} Δ⊢f∙a∷T Γ⊢γ⇒Δ = let
    A , B , Δ⊢PiAB , Δ⊢f∷PiAB , Δ⊢a∷A , Δ⊢T≡B[id◀a] = appTmInversion Δ⊢f∙a∷T
    Δ⊢A , Δ◁A⊢B = piTyInversion Δ⊢PiAB
    ⊢Δ = tyWfCtx Δ⊢A
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ⊢a[γ]∷A[γ] = TmSubst Δ⊢a∷A Γ⊢γ⇒Δ
    Δ⊢id◀a⇒Δ◁A = section Δ⊢A Δ⊢a∷A
    Γ⊢id◀a[γ]⇒Γ◁A[γ] = section Γ⊢A[γ] Γ⊢a[γ]∷A[γ]
    Γ◁A[γ]⊢liftγ⇒Δ◁A = liftSb Γ⊢γ⇒Δ Δ⊢A
    open TyEqReason
    Γ⊢liftγ∘id◀a[γ]≡id◀a∘γ⇒Δ◁A = liftSectionCommute Γ⊢γ⇒Δ Δ⊢A Δ⊢a∷A
    Γ⊢B[liftγ][id◀a]≡T[γ] = 
      Γ ⊢begin-ty
        B [ lift γ ]ₑ [ idₛ ◀ a [ γ ]ₑ ]ₑ
      ty-≡⟨ TyEqSubstSubst Δ◁A⊢B Γ◁A[γ]⊢liftγ⇒Δ◁A Γ⊢id◀a[γ]⇒Γ◁A[γ] ⟩
        B [ lift γ ∘ idₛ ◀ a [ γ ]ₑ ]ₑ
      ty-≡⟨ tyEqSubst₂ Δ◁A⊢B Γ⊢liftγ∘id◀a[γ]≡id◀a∘γ⇒Δ◁A ⟩
        B [ idₛ ◀ a ∘ γ ]ₑ
      ty-≡⟨ TyEqSubstSubst Δ◁A⊢B Δ⊢id◀a⇒Δ◁A Γ⊢γ⇒Δ ⟨
        B [ idₛ ◀ a ]ₑ [ γ ]ₑ
      ty-≡⟨ tyEqSubst₁ Δ⊢T≡B[id◀a] Γ⊢γ⇒Δ ⟨∣
        T [ γ ]ₑ
      ∎
      
    Γ⊢f[γ]∙a[γ]∷T[γ] =
      begin
        intro-⟨ Δ⊢f∷PiAB ⟩  Δ ⊢ f ∷ Pi A B
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢γ⇒Δ ⟩
        Γ ⊢ f [ γ ]ₑ ∷ Pi A B [ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ) ⟩
        Γ ⊢ f [ γ ]ₑ ∷ Pi (A [ γ ]ₑ) (B [ lift γ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-App-on  Γ⊢a[γ]∷A[γ] ⟩
        Γ ⊢ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ B [ lift γ ]ₑ [ idₛ ◀ a [ γ ]ₑ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by Γ⊢B[liftγ][id◀a]≡T[γ] ⟩
        Γ ⊢ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ T [ γ ]ₑ
      ∎
  in (TmSubst Δ⊢f∙a∷T Γ⊢γ⇒Δ) , Γ⊢f[γ]∙a[γ]∷T[γ]
...| TmEqNatSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Γ⊢Nat∷U[γ] = TmSubst (TmNat ⊢Δ) Γ⊢γ⇒Δ
  in TmTyConv Γ⊢Nat∷U[γ] (TyEqUSubst Γ⊢γ⇒Δ) , TmNat ⊢Γ
...| TmEqZeroSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Γ⊢Zero∷Nat[γ] = TmSubst (TmZero ⊢Δ) Γ⊢γ⇒Δ
  in TmTyConv Γ⊢Zero∷Nat[γ] (TyEqNatSubst Γ⊢γ⇒Δ) , TmZero ⊢Γ
...| TmEqSuccSubst Δ⊢Succ-a∷Nat Γ⊢γ⇒Δ = let
    Δ⊢a∷Nat , _ = succTmInversion Δ⊢Succ-a∷Nat
    Γ⊢Nat[γ]≡Nat = TyEqNatSubst Γ⊢γ⇒Δ
    Γ⊢a[γ]∷Nat[γ] = TmSubst Δ⊢a∷Nat Γ⊢γ⇒Δ
    Γ⊢a[γ]∷Nat = TmTyConv Γ⊢a[γ]∷Nat[γ] Γ⊢Nat[γ]≡Nat
    Γ⊢Succ-a[γ]∷Nat[γ] = TmSubst Δ⊢Succ-a∷Nat Γ⊢γ⇒Δ
  in TmTyConv Γ⊢Succ-a[γ]∷Nat[γ] Γ⊢Nat[γ]≡Nat , TmSucc Γ⊢a[γ]∷Nat
...| TmEqNatElimSubst {Δ} {A} {a} {b} {c} {Γ} {γ} Δ⊢NatElim∷A[id◀c] Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Δ◁ℕ⊢A , Δ⊢a∷A[id◀Z] , Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Δ⊢c∷Nat , _ = natElimTmInversion Δ⊢NatElim∷A[id◀c]
    Γ⊢ℕ[γ]≡ℕ = TyEqNatSubst Γ⊢γ⇒Δ
    Δ⊢ℕ = TyNat ⊢Δ
    Γ⊢ℕ = TyNat ⊢Γ
    ⊢Γ◁ℕ[γ]≡Γ◁ℕ = ctxEqExt₂ ⊢Γ (TySubst Δ⊢ℕ Γ⊢γ⇒Δ) Γ⊢ℕ  Γ⊢ℕ[γ]≡ℕ
    Γ⊢id⇒Γ = SbId ⊢Γ
    Γ⊢c[γ]∷ℕ = TmTyConv (TmSubst Δ⊢c∷Nat Γ⊢γ⇒Δ) Γ⊢ℕ[γ]≡ℕ
    Γ◁ℕ⊢lift-γ⇒Δ◁ℕ = sbStability ⊢Γ◁ℕ[γ]≡Γ◁ℕ (liftSb Γ⊢γ⇒Δ Δ⊢ℕ)
    Γ◁ℕ◁A[lift-γ]⊢lift-lift-γ⇒Δ◁ℕ◁A = liftSb Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Δ◁ℕ⊢A
    Γ◁ℕ⊢A[lift-γ] = TySubst Δ◁ℕ⊢A Γ◁ℕ⊢lift-γ⇒Δ◁ℕ
    Γ◁ℕ◁A[lift-γ]⊢SVar1∷ℕ = TmSucc (natVarˢ (natVarᶻ ⊢Γ) Γ◁ℕ⊢A[lift-γ])
    Γ◁ℕ◁A[lift-γ]⊢drop1⇒Γ◁ℕ = display Γ◁ℕ⊢A[lift-γ]
    Δ◁ℕ◁A⊢drop2⇒Δ = drop2 Δ⊢ℕ Δ◁ℕ⊢A
    Δ◁ℕ⊢SVar0∷ℕ = TmSucc (natVarᶻ ⊢Δ)
    Δ◁ℕ⊢SVar0∷ℕ[drop1] = TmTyConv Δ◁ℕ⊢SVar0∷ℕ (TyEqSym (TyEqNatSubst (display Δ⊢ℕ)))
    Δ◁ℕ◁A⊢SVar1∷ℕ = TmSucc (natVarˢ (natVarᶻ ⊢Δ) Δ◁ℕ⊢A)
    Δ◁ℕ◁A⊢SVar1∷ℕ[drop2] = TmTyConv Δ◁ℕ◁A⊢SVar1∷ℕ (TyEqSym (TyEqNatSubst Δ◁ℕ◁A⊢drop2⇒Δ))
    Γ◁ℕ◁A[lift-γ]⊢drop2◀SVar1⇒Γ◁ℕ = sbExtNat (drop2 Γ⊢ℕ Γ◁ℕ⊢A[lift-γ]) Γ◁ℕ◁A[lift-γ]⊢SVar1∷ℕ
    Δ◁ℕ◁A⊢drop2◀SVar1⇒Δ◁ℕ = sbExtNat Δ◁ℕ◁A⊢drop2⇒Δ Δ◁ℕ◁A⊢SVar1∷ℕ
    Δ◁ℕ⊢drop1◀SVar0⇒Δ◁ℕ = sbExtNat (display Δ⊢ℕ) Δ◁ℕ⊢SVar0∷ℕ
    Γ◁ℕ⊢drop1◀SVar0⇒Γ◁ℕ = sbExtNat (display Γ⊢ℕ) (TmSucc (natVarᶻ ⊢Γ))
    

    Γ⊢Z[γ]≡Z∷Nat[id] = TmEqConv (TmEqZeroSubst Γ⊢γ⇒Δ) (TyEqSym (TyEqNatSubst Γ⊢id⇒Γ))
    Δ⊢id◀Z⇒Δ◁ℕ = section Δ⊢ℕ (TmZero ⊢Δ)
    Γ⊢id◀Z⇒Γ◁ℕ = section Γ⊢ℕ (TmZero ⊢Γ)

    open TyEqReason
    open SbEqReason
    open TmHEqReason

    Γ◁ℕ⊢SVar0≡SVar0[lift-γ]∷ℕ[drop1] = 
      Γ ◁ Nat ⊢begin-heqₗ
        Succ (Var 0) ∷ Nat [ drop 1 ]ₑ
      heq-≡⟨∷ TyEqNatSubst (display Γ⊢ℕ) ∷⟩
        Succ (Var 0) ∷ Nat
      heq-≡⟨∣ hTmEqSuccEqᵣ (HTmEqₗ (TyEqNatSubst Γ◁ℕ⊢lift-γ⇒Δ◁ℕ) (TmEqSubstVarExt (natVarᶻ ⊢Δ) Γ◁ℕ⊢lift-γ⇒Δ◁ℕ)) ∙⟨ 
        Succ (Var 0 [ lift γ ]ₑ) ∷ Nat [ lift γ ]ₑ
      heq-≡⟨∷ TyEqNatSubst Γ◁ℕ⊢lift-γ⇒Δ◁ℕ ∷⟩
        Succ (Var 0 [ lift γ ]ₑ) ∷ Nat
      heq-≡⟨  TmEqSuccSubst Δ◁ℕ⊢SVar0∷ℕ Γ◁ℕ⊢lift-γ⇒Δ◁ℕ  ⟨∣ (TyNat (ctxExt Γ⊢ℕ)) ∣
        Succ (Var 0) [ lift γ ]ₑ ∷ Nat
      ∎

    Γ⊢id◀Z∘γ≡lift-γ∘id◀Z⇒Δ◁ℕ = 
      Γ ⊢begin-sb
        idₛ ◀ Zero ∘ γ
      sb-≡⟨ liftSectionCommute Γ⊢γ⇒Δ Δ⊢ℕ (TmZero ⊢Δ) ⟨
        lift γ ∘ idₛ ◀ Zero [ γ ]ₑ
      sb-≡⟨ sbEqComp₂ Γ◁ℕ⊢lift-γ⇒Δ◁ℕ (sbEqExt₂ (SbId ⊢Γ) Γ⊢ℕ Γ⊢Z[γ]≡Z∷Nat[id]) ⟩∣
        lift γ ∘ idₛ ◀ Zero
      ∎⇒ Δ ◁ Nat
    
    Γ◁ℕ⊢drop1◀SVar0∘lift-γ≡lift-γ∘drop1◀SVar0⇒Δ◁ℕ = 
      Γ ◁ Nat ⊢begin-sb
        drop 1 ◀ Succ (Var 0) ∘ lift γ
      sb-≡⟨ sbEqStability ⊢Γ◁ℕ[γ]≡Γ◁ℕ (liftComm Γ⊢γ⇒Δ Δ⊢ℕ Δ◁ℕ⊢SVar0∷ℕ[drop1]) ⟩
        lift γ ∘ drop 1 ◀ Succ (Var 0) [ lift γ ]ₑ
      sb-≡⟨ sbEqComp₂ Γ◁ℕ⊢lift-γ⇒Δ◁ℕ (sbEqExt₂ (display Γ⊢ℕ)Γ⊢ℕ (TmEqSym Γ◁ℕ⊢SVar0≡SVar0[lift-γ]∷ℕ[drop1])) ⟩∣
        lift γ ∘ drop 1 ◀ Succ (Var 0)
      ∎⇒ Δ ◁ Nat

    Γ◁ℕ◁A[lift-γ]⊢drop2◀SVar1∘lift-lift-γ≡lift-γ∘drop2◀SVar1⇒Δ◁ℕ = 
       Γ ◁ Nat ◁ A [ lift γ ]ₑ ⊢begin-sb
        drop 2 ◀ Succ (Var 1) ∘ lift (lift γ)
      sb-≡⟨ sbEqComp₁ (drop2SucExpEq Δ◁ℕ⊢A) Γ◁ℕ◁A[lift-γ]⊢lift-lift-γ⇒Δ◁ℕ◁A ⟩
        drop 1 ◀ Succ (Var 0) ∘ drop 1 ∘ lift (lift γ)
      sb-≡⟨ SbEqCompAssoc Δ◁ℕ⊢drop1◀SVar0⇒Δ◁ℕ (display Δ◁ℕ⊢A) Γ◁ℕ◁A[lift-γ]⊢lift-lift-γ⇒Δ◁ℕ◁A ⟩
        drop 1 ◀ Succ (Var 0) ∘ (drop 1 ∘ lift (lift γ))
      sb-≡⟨ sbEqComp₂ Δ◁ℕ⊢drop1◀SVar0⇒Δ◁ℕ (liftDropComm Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Δ◁ℕ⊢A) ⟩
        drop 1 ◀ Succ (Var 0) ∘ (lift γ ∘ drop 1)
      sb-≡⟨ SbEqCompAssoc Δ◁ℕ⊢drop1◀SVar0⇒Δ◁ℕ Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Γ◁ℕ◁A[lift-γ]⊢drop1⇒Γ◁ℕ ⟨
        drop 1 ◀ Succ (Var 0) ∘ lift γ ∘ drop 1
      sb-≡⟨ sbEqComp₁ Γ◁ℕ⊢drop1◀SVar0∘lift-γ≡lift-γ∘drop1◀SVar0⇒Δ◁ℕ Γ◁ℕ◁A[lift-γ]⊢drop1⇒Γ◁ℕ ⟩
        lift γ ∘ drop 1 ◀ Succ (Var 0) ∘ drop 1
      sb-≡⟨ SbEqCompAssoc Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Γ◁ℕ⊢drop1◀SVar0⇒Γ◁ℕ Γ◁ℕ◁A[lift-γ]⊢drop1⇒Γ◁ℕ ⟩
        lift γ ∘ (drop 1 ◀ Succ (Var 0) ∘ drop 1)
      sb-≡⟨ sbEqComp₂ Γ◁ℕ⊢lift-γ⇒Δ◁ℕ (drop2SucExpEq Γ◁ℕ⊢A[lift-γ]) ⟨∣
        lift γ ∘ drop 2 ◀ Succ (Var 1)
      ∎⇒ Δ ◁ Nat


    Γ⊢a[γ]∷A[lift-γ][id◀Z] = 
      begin
        intro-⟨ Δ⊢a∷A[id◀Z] ⟩
        (Δ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢γ⇒Δ ⟩
        (Γ ⊢ a [ γ ]ₑ ∷ A [ idₛ ◀ Zero ]ₑ [ γ ]ₑ) 
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Δ◁ℕ⊢A Δ⊢id◀Z⇒Δ◁ℕ  Γ⊢γ⇒Δ) ⟩
        (Γ ⊢ a [ γ ]ₑ ∷ A [ idₛ ◀ Zero ∘ γ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ◁ℕ⊢A Γ⊢id◀Z∘γ≡lift-γ∘id◀Z⇒Δ◁ℕ) ⟩
        (Γ ⊢ a [ γ ]ₑ ∷ A [ lift γ ∘ idₛ ◀ Zero ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Δ◁ℕ⊢A Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Γ⊢id◀Z⇒Γ◁ℕ) ⟩
        (Γ ⊢ a [ γ ]ₑ ∷ A [ lift γ ]ₑ [ idₛ ◀ Zero ]ₑ) 
      ∎

    Γ◁ℕ◁A[lift-γ]⊢b[lift-lift-γ]∷A[lift-γ][drop2◀SVar1] = 
      begin
        intro-⟨ Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] ⟩
          Δ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ
        ⎯⎯⎯⎯⟨ Tm-Subst-by Γ◁ℕ◁A[lift-γ]⊢lift-lift-γ⇒Δ◁ℕ◁A  ⟩
          Γ ◁ Nat ◁ A [ lift γ ]ₑ ⊢ b [ lift (lift γ) ]ₑ ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ [ lift (lift γ) ]ₑ
        ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst  Δ◁ℕ⊢A Δ◁ℕ◁A⊢drop2◀SVar1⇒Δ◁ℕ Γ◁ℕ◁A[lift-γ]⊢lift-lift-γ⇒Δ◁ℕ◁A) ⟩
          Γ ◁ Nat ◁ A [ lift γ ]ₑ ⊢ b [ lift (lift γ) ]ₑ ∷ A [ drop 2 ◀ Succ (Var 1) ∘ lift (lift γ) ]ₑ
        ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ◁ℕ⊢A Γ◁ℕ◁A[lift-γ]⊢drop2◀SVar1∘lift-lift-γ≡lift-γ∘drop2◀SVar1⇒Δ◁ℕ) ⟩
          Γ ◁ Nat ◁ A [ lift γ ]ₑ ⊢ b [ lift (lift γ) ]ₑ ∷ A [ lift γ ∘ drop 2 ◀ Succ (Var 1) ]ₑ
        ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Δ◁ℕ⊢A Γ◁ℕ⊢lift-γ⇒Δ◁ℕ Γ◁ℕ◁A[lift-γ]⊢drop2◀SVar1⇒Γ◁ℕ) ⟩
          Γ ◁ Nat ◁ A [ lift γ ]ₑ ⊢ b [ lift (lift γ) ]ₑ ∷ A [ lift γ ]ₑ [ drop 2 ◀ Succ (Var 1) ]ₑ
     ∎ 
    
    natElim = TmNatElim Γ◁ℕ⊢A[lift-γ] Γ⊢a[γ]∷A[lift-γ][id◀Z] Γ◁ℕ◁A[lift-γ]⊢b[lift-lift-γ]∷A[lift-γ][drop2◀SVar1] Γ⊢c[γ]∷ℕ
    Γ⊢NatElim[γ]∷A[id◀c][γ] = 
      begin
        intro-⟨ natElim ⟩
        (Γ ⊢ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ lift γ ]ₑ [ idₛ ◀ c [ γ ]ₑ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Δ◁ℕ⊢A  Γ◁ℕ⊢lift-γ⇒Δ◁ℕ (section Γ⊢ℕ Γ⊢c[γ]∷ℕ)) ⟩
        (Γ ⊢ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ lift γ ∘ idₛ ◀ c [ γ ]ₑ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ◁ℕ⊢A (liftSectionCommute Γ⊢γ⇒Δ Δ⊢ℕ Δ⊢c∷Nat)) ⟩
        (Γ ⊢ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ idₛ ◀ c ∘ γ ]ₑ)
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Δ◁ℕ⊢A (section Δ⊢ℕ Δ⊢c∷Nat) Γ⊢γ⇒Δ) ⟩
        (Γ ⊢ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ idₛ ◀ c ]ₑ [ γ ]ₑ)
      ∎
  in TmSubst Δ⊢NatElim∷A[id◀c] Γ⊢γ⇒Δ , Γ⊢NatElim[γ]∷A[id◀c][γ]
...| TmEqSubstSubst {Δ} {δ} {Ξ} {Γ} {γ} {a} {A} Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A = let
    Ξ⊢A = tmWfTy Ξ⊢a∷A
    Γ⊢a[δ∘γ]∷A[δ][γ] = 
      begin
      intro-⟨ Δ⊢δ⇒Ξ ⟩  Δ ⊢ δ ⇒ Ξ
      ∧-intro-⟨ Γ⊢γ⇒Δ ⟩  Γ ⊢ γ ⇒ Δ
      ⎯⎯⎯⎯⟨ Sb-Comp ⟩
        Γ ⊢ δ ∘ γ ⇒ Ξ
      ⎯⎯⎯⎯⟨ Tm-Subst-on Ξ⊢a∷A ⟩
        Γ ⊢ a [ δ ∘ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Ξ⊢A Δ⊢δ⇒Ξ Γ⊢γ⇒Δ) ⟩
        Γ ⊢ a [ δ ∘ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ
      ∎
  in TmSubst (TmSubst Ξ⊢a∷A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ , Γ⊢a[δ∘γ]∷A[δ][γ]
...| TmEqUSubst Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Γ⊢Ul∷USl[γ] = TmSubst (TmUniv ⊢Δ) Γ⊢γ⇒Δ
  in TmTyConv Γ⊢Ul∷USl[γ] (TyEqUSubst Γ⊢γ⇒Δ) , TmUniv ⊢Γ
...| TmEqPiBeta Γ⊢A Γ◁A⊢b∷B Γ⊢a∷A = let
    Γ⊢Lam-b∷PiAB = TmLam Γ⊢A Γ◁A⊢b∷B
    Γ⊢id◀a⇒Γ◁A = section Γ⊢A Γ⊢a∷A
  in TmApp Γ⊢Lam-b∷PiAB Γ⊢a∷A , TmSubst Γ◁A⊢b∷B Γ⊢id◀a⇒Γ◁A
...| TmEqNatElimZero Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] = let
    ⊢Γ = tmWfCtx Γ⊢a∷A[id◀Z]
    Γ⊢Zero∷ℕ = TmZero ⊢Γ
  in TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢Zero∷ℕ , Γ⊢a∷A[id◀Z]
...| TmEqNatElimSucc {Γ} {A} {a} {b} {c} Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢A[drop2◀SVar1] Γ⊢c∷ℕ = let
    Γ⊢ℕ = tmWfTy Γ⊢c∷ℕ
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    ⊢Γ◁ℕ = ctxExt Γ⊢ℕ
    Γ⊢sc∷ℕ = TmSucc Γ⊢c∷ℕ
    Γ⊢id◀c⇒Γ◁ℕ = section Γ⊢ℕ Γ⊢c∷ℕ
    Γ⊢NatElim-c∷A[id◀c] = TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢A[drop2◀SVar1] Γ⊢c∷ℕ
    Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A = SbExt Γ⊢id◀c⇒Γ◁ℕ Γ◁ℕ⊢A Γ⊢NatElim-c∷A[id◀c]
    Γ◁ℕ◁A⊢SVar1∷ℕ = TmSucc (natVarˢ (natVarᶻ ⊢Γ) Γ◁ℕ⊢A)
    Γ◁ℕ◁A⊢drop2⇒Γ = drop2 Γ⊢ℕ Γ◁ℕ⊢A
    Γ◁ℕ◁A⊢drop2◀SVar1⇒Γ◁ℕ = sbExtNat Γ◁ℕ◁A⊢drop2⇒Γ  Γ◁ℕ◁A⊢SVar1∷ℕ
    varEq = varSbˢ Γ⊢id◀c⇒Γ◁ℕ (TyNat ⊢Γ◁ℕ) (natVarᶻ ⊢Γ) Γ◁ℕ⊢A Γ⊢NatElim-c∷A[id◀c] (TmEqSubstVarExt (natVarᶻ ⊢Γ)  Γ⊢id◀c⇒Γ◁ℕ)
    open SbEqReason
    open TmHEqReason

    extEq = 
      Γ ⊢begin-heqᵣ
        Succ (Var 1) [ idₛ ◀ c ◀ NatElim A a b c ]ₑ ∷ Nat
      heq-≡⟨ TmEqSuccSubst Γ◁ℕ◁A⊢SVar1∷ℕ Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A ⟩
        Succ (Var 1 [ idₛ ◀ c ◀ NatElim A a b c ]ₑ) ∷ Nat
      heq-≡⟨ TmEqSucc (TmEqConv varEq (TyEqNatSubst Γ⊢id◀c⇒Γ◁ℕ)) ⟩ 
        Succ c ∷ Nat
      heq-≡⟨∷ TyEqNatSubst (SbComp Γ◁ℕ◁A⊢drop2⇒Γ Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A) ∷⟨∣ 
        Γ⊢sc∷ℕ
      ⟨∎∷ Nat [ drop 2 ∘ idₛ ◀ c ◀ NatElim A a b c ]ₑ
    sbEq =
      Γ ⊢begin-sb
        drop 2 ◀ Succ (Var 1) ∘ idₛ ◀ c ◀ NatElim A a b c
      sb-≡⟨ SbEqExtComp Γ◁ℕ◁A⊢drop2◀SVar1⇒Γ◁ℕ Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A ⟩
        (drop 2 ∘ idₛ ◀ c ◀ NatElim A a b c) ◀ Succ (Var 1) [ idₛ ◀ c ◀ NatElim A a b c ]ₑ
      sb-≡⟨ SbEqExt (drop2Ext2Eq Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A) Γ⊢ℕ extEq ⟩∣
        idₛ ◀ Succ c
      ∎⇒ Γ ◁ Nat
  in TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢A[drop2◀SVar1] Γ⊢sc∷ℕ , (
    begin
      intro-⟨ Γ◁ℕ◁A⊢A[drop2◀SVar1] ⟩
      Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A ⟩
      Γ ⊢ b [ idₛ ◀ c ◀ NatElim A a b c ]ₑ ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ [ idₛ ◀ c ◀ NatElim A a b c ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Γ◁ℕ⊢A Γ◁ℕ◁A⊢drop2◀SVar1⇒Γ◁ℕ Γ⊢id◀c◀NatElim-c⇒Γ◁ℕ◁A) ⟩
      Γ ⊢ b [ idₛ ◀ c ◀ NatElim A a b c ]ₑ ∷ A [ drop 2 ◀ Succ (Var 1) ∘ idₛ ◀ c ◀ NatElim A a b c ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Γ◁ℕ⊢A sbEq) ⟩
      Γ ⊢ b [ idₛ ◀ c ◀ NatElim A a b c ]ₑ ∷ A [ idₛ ◀ Succ c ]ₑ
    ∎)
...| TmEqPiEta {Γ} {f} {A} {B} Γ⊢f∷PiAB = let
    Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
    Γ⊢A , Γ◁A⊢B = piTyInversion Γ⊢PiAB
    ⊢Γ◁A = ctxExt Γ⊢A
    Γ◁A⊢drop1⇒Γ = display Γ⊢A
    Γ◁A⊢A[drop1] = TySubst Γ⊢A Γ◁A⊢drop1⇒Γ
    Γ◁A⊢var0∷A[drop1] = TmVarᶻ Γ⊢A
    Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] = section Γ◁A⊢A[drop1] Γ◁A⊢var0∷A[drop1]
    Γ◁A◁A[drop1]⊢lift[drop1]⇒Γ◁A = liftSb Γ◁A⊢drop1⇒Γ Γ⊢A
    open TyEqReason
    tyEq = 
      Γ ◁ A ⊢begin-ty
        B [ lift (drop 1) ]ₑ [ idₛ ◀ Var 0 ]ₑ
      ty-≡⟨ TyEqSubstSubst Γ◁A⊢B Γ◁A◁A[drop1]⊢lift[drop1]⇒Γ◁A Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] ⟩
        B [ lift (drop 1) ∘ idₛ ◀ Var 0 ]ₑ
      ty-≡⟨ tyEqSubst₂ Γ◁A⊢B (liftDropEq Γ⊢A) ⟩
        B [ idₛ ]ₑ
      ty-≡⟨ TyEqSubstId Γ◁A⊢B ⟩∣
        B
      ∎

    Γ⊢Lam[f[drop1]∙Var0]∷PiAB = 
      begin
        intro-⟨ Γ⊢f∷PiAB ⟩  Γ ⊢ f ∷ Pi A B  
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ◁A⊢drop1⇒Γ ⟩
        Γ ◁ A ⊢ f [ drop 1 ]ₑ ∷ Pi A B [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqPiSubst Γ⊢PiAB Γ◁A⊢drop1⇒Γ) ⟩
        Γ ◁ A ⊢ f [ drop 1 ]ₑ ∷ Pi (A [ drop 1 ]ₑ) (B [ lift (drop 1) ]ₑ) 
      ⎯⎯⎯⎯⟨ Tm-App-on Γ◁A⊢var0∷A[drop1] ⟩
        Γ ◁ A ⊢ (f [ drop 1 ]ₑ) ∙ Var 0 ∷ B [ lift (drop 1) ]ₑ [ idₛ ◀ Var 0 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by tyEq ⟩
        Γ ◁ A ⊢ (f [ drop 1 ]ₑ) ∙ Var 0 ∷ B
      ⎯⎯⎯⎯⟨ Tm-Lam-abs Γ⊢A ⟩
        Γ ⊢ Lam ((f [ drop 1 ]ₑ) ∙ Var 0) ∷ Pi A B
      ∎
  in Γ⊢f∷PiAB , Γ⊢Lam[f[drop1]∙Var0]∷PiAB
...| TmEqNatEta {Γ} {c} Γ⊢c∷ℕ = let
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    Γ⊢ℕ = TyNat ⊢Γ
    ⊢Γ◁ℕ = ctxExt Γ⊢ℕ
    Γ◁ℕ⊢ℕ = TyNat ⊢Γ◁ℕ
    Γ⊢Z∷ℕ = TmZero ⊢Γ
    Γ⊢id◀c⇒Γ◁ℕ = section Γ⊢ℕ Γ⊢c∷ℕ
    Γ⊢id◀Z⇒Γ◁ℕ = section Γ⊢ℕ Γ⊢Z∷ℕ
    Γ◁ℕ◁ℕ⊢SVar0∷ℕ = TmSucc (natVarᶻ ⊢Γ◁ℕ)
    Γ◁ℕ◁ℕ⊢SVar1∷ℕ = TmSucc (natVarˢ (natVarᶻ ⊢Γ) Γ◁ℕ⊢ℕ)
    Γ◁ℕ◁ℕ⊢drop2⇒Γ = drop2 Γ⊢ℕ Γ◁ℕ⊢ℕ
    Γ◁ℕ◁ℕ⊢SVar1∷ℕ[drop2] = TmTyConv Γ◁ℕ◁ℕ⊢SVar1∷ℕ (TyEqSym (TyEqNatSubst Γ◁ℕ◁ℕ⊢drop2⇒Γ))
    Γ◁ℕ◁ℕ⊢drop2◀SVar1⇒Γ◁ℕ = SbExt Γ◁ℕ◁ℕ⊢drop2⇒Γ Γ⊢ℕ Γ◁ℕ◁ℕ⊢SVar1∷ℕ[drop2]
    Γ◁ℕ◁ℕ⊢SVar0∷ℕ[drop2◀SVar1] = TmTyConv Γ◁ℕ◁ℕ⊢SVar0∷ℕ (TyEqSym (TyEqNatSubst Γ◁ℕ◁ℕ⊢drop2◀SVar1⇒Γ◁ℕ))
    Γ⊢Z∷ℕ[id◀Z] = TmTyConv Γ⊢Z∷ℕ (TyEqSym (TyEqNatSubst Γ⊢id◀Z⇒Γ◁ℕ))
  in TmTyConv (TmNatElim Γ◁ℕ⊢ℕ Γ⊢Z∷ℕ[id◀Z] Γ◁ℕ◁ℕ⊢SVar0∷ℕ[drop2◀SVar1] Γ⊢c∷ℕ) (TyEqNatSubst Γ⊢id◀c⇒Γ◁ℕ) , Γ⊢c∷ℕ

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
    varExist Γ' B Γ'⊢B Γ⊢drop1⇒Γ' Γ⊢id⇒Γ'◁B , Γ⊢A≡B[drop1] = varTmInversion Γ⊢Var0∷A
    ⊢Γ = tmWfCtx Γ⊢Var0∷A
    ⊢Γ≡Γ'◁B = idInversion Γ⊢id⇒Γ'◁B
  in (
      begin
        intro-⟨ Γ⊢Var0∷A ⟩  Γ ⊢ Var 0 ∷ A
      ⎯⎯⎯⎯⟨ Tm-TyConv-by Γ⊢A≡B[drop1] ⟩
        Γ ⊢ Var 0 ∷ B [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ SbExt Γ⊢drop1⇒Γ' Γ'⊢B  ⟩
        Γ ⊢ drop 1 ◀ Var 0 ⇒ Γ' ◁ B
      ⎯⎯⎯⎯⟨ Sb-Conv-by' ⊢Γ≡Γ'◁B  ⟩
        Γ ⊢ drop 1 ◀ Var 0 ⇒ Γ
      ∎
    ) , (SbId ⊢Γ)
...| SbEqDropExt Δ⊢drop1⇒Ξ Γ⊢γ◀a⇒Δ = let 
    Γ⊢drop1∘[γ◀a]⇒Ξ = SbComp Δ⊢drop1⇒Ξ Γ⊢γ◀a⇒Δ
    ctxExtInv _ _ Δ'⊢A ⊢Δ≡Δ'◁A , Γ⊢γ⇒Δ' , Γ⊢a∷Aγ = sbExtInversion Γ⊢γ◀a⇒Δ
    ctxExtInv _ _ Δ''⊢A ⊢Δ≡Δ''◁A , ⊢Δ''≡Ξ = drop1Inversion Δ⊢drop1⇒Ξ
    ⊢Δ'◁A≡Δ''◁A = ctxEqTrans (ctxEqSym ⊢Δ≡Δ'◁A) ⊢Δ≡Δ''◁A
    ⊢Δ'≡Δ'' = proj₁ (ctxEqExtInversion ⊢Δ'◁A≡Δ''◁A)
    ⊢Δ'≡Ξ = ctxEqTrans ⊢Δ'≡Δ'' ⊢Δ''≡Ξ
    Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ' ⊢Δ'≡Ξ
  in Γ⊢drop1∘[γ◀a]⇒Ξ , Γ⊢γ⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ = let 
    Γ⊢dropX∘drop1⇒Ξ = SbComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ
    ctxExtInv _ _ Γ'⊢A ⊢Γ≡Γ'◁A , ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
    Γ'⊢dropX⇒Ξ = sbStability' ⊢Γ'≡Δ Δ⊢dropX⇒Ξ
    Γ'◁A⊢dropSX⇒Ξ = SbDropˢ Γ'⊢dropX⇒Ξ Γ'⊢A
    Γ⊢dropSX⇒Ξ = sbStability' ⊢Γ≡Γ'◁A Γ'◁A⊢dropSX⇒Ξ
  in Γ⊢dropX∘drop1⇒Ξ , Γ⊢dropSX⇒Ξ
...| SbEqExtComp {Δ} {δ} {a} {Ξ} {Γ} {γ} Δ⊢δ◀a⇒Ξ Γ⊢γ⇒Δ = let 
    ctxExtInv Ξ₁ A Ξ₁⊢A ⊢Ξ≡Ξ₁◁A , Δ⊢δ⇒Ξ₁ , Δ⊢a∷Aδ = sbExtInversion Δ⊢δ◀a⇒Ξ
  in (SbComp Δ⊢δ◀a⇒Ξ Γ⊢γ⇒Δ) , (
      begin
        intro-⟨ Δ⊢a∷Aδ ⟩  Δ ⊢ a ∷ A [ δ ]ₑ  
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ⊢γ⇒Δ ⟩
        Γ ⊢ a [ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Ξ₁⊢A Δ⊢δ⇒Ξ₁ Γ⊢γ⇒Δ) ⟩
        Γ ⊢ a [ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
      ⎯⎯⎯⎯⟨ Sb-Ext-to (SbComp Δ⊢δ⇒Ξ₁ Γ⊢γ⇒Δ) Ξ₁⊢A ⟩
        Γ ⊢ (δ ∘ γ) ◀ a [ γ ]ₑ  ⇒ Ξ₁ ◁ A
      ⎯⎯⎯⎯⟨ Sb-Conv-by' ⊢Ξ≡Ξ₁◁A ⟩
        Γ ⊢ (δ ∘ γ) ◀ a [ γ ]ₑ  ⇒ Ξ
      ∎
    ) 

