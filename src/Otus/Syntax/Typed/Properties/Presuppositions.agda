{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Presuppositions where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Inversion.Base

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term

ctxEqWfCtx : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
tyWfCtx : Γ ⊢ A → ⊢ Γ
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ

substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ × ⊢ Δ
tyEqWfCtx : Γ ⊢ A ≡ⱼ B → ⊢ Γ
tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ

ctxExt : Γ ⊢ A → ⊢ Γ ▷ A
ctxExt Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A

-- substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
substWfCtx sb with sb
...| SbId ⊢Γ = ⊢Γ , ⊢Γ
...| SbDropˢ Γ⇒Δ Γ⊢A = let 
    ⊢Γ , ⊢Δ = substWfCtx Γ⇒Δ
  in (CExt ⊢Γ Γ⊢A) , ⊢Δ
...| SbExt Γ⇒Δ Δ⊢A Γ⊢a∷Aγ = let 
    ⊢Γ , ⊢Δ = substWfCtx Γ⇒Δ
    ⊢Δ▷A = (CExt ⊢Δ Δ⊢A)
  in ⊢Γ , ⊢Δ▷A
...| SbComp Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)
...| SbConv Γ⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₁₂ (substWfCtx Γ⇒Δ₁) (ctxEqWfCtx ⊢Δ₁≡Δ₂)


-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyWfCtx ty with ty
...| TyPi Γ⊢A Γ▷A⊢B = tyWfCtx Γ⊢A 
...| TyU ⊢Γ = ⊢Γ
...| TySubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TyRussel Γ⊢A∷U = tmWfCtx Γ⊢A∷U

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmWfCtx tm with tm
...| TmVarᶻ Γ⊢A = ctxExt Γ⊢A
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = CExt (tmWfCtx Γ⊢VarX∷A) Γ⊢B
...| TmLam _ Γ▷A⊢b∷B = proj₁ (ctxExtInversion (tmWfCtx Γ▷A⊢b∷B))
...| TmPi Γ⊢A∷U _ = tmWfCtx Γ⊢A∷U
...| TmApp _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TmU ⊢Γ = ⊢Γ
...| TmTyConv Γ⊢a∷A _ = tmWfCtx Γ⊢a∷A

-- 

-- ctxEqWfCtx : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWfCtx eq with eq
...| CEqRefl ⊢Γ = ⊢Γ , ⊢Γ
...| CEqExt ⊢Γ≡Δ Γ⊢A Δ⊢B _ = let 
    ⊢Γ , ⊢Δ = ctxEqWfCtx ⊢Γ≡Δ
  in (CExt ⊢Γ Γ⊢A) , (CExt ⊢Δ Δ⊢B)

-- substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ × ⊢ Δ
substEqWfCtx eq with eq
...| SbEqRefl Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = substEqWfCtx Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A _ = let 
    ⊢Γ , ⊢Δ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
  in ⊢Γ , (CExt ⊢Δ Δ⊢A)
...| SbEqComp Δ⇒Ξ Γ⇒Δ = proj₁₂ (substEqWfCtx Γ⇒Δ) (substEqWfCtx Δ⇒Ξ)
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₁₂ (substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ₁) (ctxEqWfCtx ⊢Δ₁≡Δ₂)
...| SbEqCompAssoc Ξ⇒Θ _ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Ξ⇒Θ)
...| SbEqIdₗ Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)
...| SbEqIdᵣ Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)
...| SbEqExtVar Γ⇒Δ _ = substWfCtx Γ⇒Δ
...| SbEqDropExt Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)
...| SbEqDropComp Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)
...| SbEqExtComp Δ⇒Ξ Γ⇒Δ = proj₁₂ (substWfCtx Γ⇒Δ) (substWfCtx Δ⇒Ξ)

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyEqWfCtx ty with ty
...| TyEqRefl Γ⊢A = tyWfCtx Γ⊢A
...| TyEqSym Γ⊢B≡A = tyEqWfCtx Γ⊢B≡A
...| TyEqTrans Γ⊢A≡B Γ⊢B≡C = tyEqWfCtx Γ⊢A≡B
...| TyEqPi _ Γ⊢A≡B _ = tyEqWfCtx Γ⊢A≡B
...| TyEqSubst _ Γ⇒Δ = proj₁ (substEqWfCtx Γ⇒Δ)
...| TyEqRussel Γ⊢A≡B∷U = tmEqWfCtx Γ⊢A≡B∷U
...| TyEqPiSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TyEqUSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TyEqSubstSubst _ Γ⇒Δ _ = proj₁ (substWfCtx Γ⇒Δ)
...| TyEqSubstId Γ⊢A = tyWfCtx Γ⊢A

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmEqWfCtx tm with tm
...| TmEqRefl Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = tmEqWfCtx Γ⊢b≡a∷A
...| TmEqTrans Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqLam _ Γ▷A⊢a≡b∷B = proj₁ (ctxExtInversion (tmEqWfCtx Γ▷A⊢a≡b∷B))
...| TmEqApp _ _ Γ⊢a≡b∷A = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqPi _ Γ⊢A≡B∷U _ = tmEqWfCtx Γ⊢A≡B∷U
...| TmEqSubst _ _ Γ⊢γ₁≡γ₂⇒Δ = proj₁ (substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ)
...| TmEqConv Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqSubstId Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSubstVarExt _ Γ⊢γ▶a⇒Δ = proj₁ (substWfCtx Γ⊢γ▶a⇒Δ)
...| TmEqSubstVarDrop _ Γ⊢dropX⇒Δ = proj₁ (substWfCtx Γ⊢dropX⇒Δ)
...| TmEqLamSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TmEqAppSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TmEqSubstComp _ Γ⊢γ⇒Δ _ = proj₁ (substWfCtx Γ⊢γ⇒Δ)
...| TmEqUSubst Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TmEqPiSubst _ Γ⇒Δ = proj₁ (substWfCtx Γ⇒Δ)
...| TmEqPiBeta _ _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqPiEta Γ⊢f∷PiAB = tmWfCtx Γ⊢f∷PiAB
