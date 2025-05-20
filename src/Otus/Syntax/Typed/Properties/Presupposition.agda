{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Presupposition where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Inversion.Base

private
  variable
    Γ Δ  : Context
    γ γ₁ γ₂ : Substitution
    f a b c A B C T : Term

tyWfCtx : Γ ⊢ A → ⊢ Γ
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
sbWfCtx : Γ ⊢ γ ⇒ Δ → ⊢ Γ

tyEqWfCtx : Γ ⊢ A ≡ⱼ B → ⊢ Γ
tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ
sbEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyWfCtx ty with ty
...| TyPi Γ⊢A Γ◁A⊢B = tyWfCtx Γ⊢A 
...| TyUniv ⊢Γ = ⊢Γ
...| TySubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TyRussel Γ⊢A∷U = tmWfCtx Γ⊢A∷U

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmWfCtx tm with tm
...| TmVarᶻ Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = CExt (tmWfCtx Γ⊢VarX∷A) Γ⊢B
...| TmLam _ Γ◁A⊢b∷B = proj₁ (ctxExtInversion (tmWfCtx Γ◁A⊢b∷B))
...| TmPi Γ⊢A∷U _ = tmWfCtx Γ⊢A∷U
...| TmApp _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmUniv ⊢Γ = ⊢Γ
...| TmTyConv Γ⊢a∷A _ = tmWfCtx Γ⊢a∷A

-- sbWfCtx : Γ ⊢ γ ⇒ Δ → ⊢ Γ
sbWfCtx sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⇒Δ Γ⊢A = CExt (sbWfCtx Γ⇒Δ) Γ⊢A
...| SbExt Γ⇒Δ _ _ = sbWfCtx Γ⇒Δ
...| SbComp _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbConv Γ⇒Δ₁ _ = sbWfCtx Γ⇒Δ₁

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyEqWfCtx ty with ty
...| TyEqRefl Γ⊢A = tyWfCtx Γ⊢A
...| TyEqSym Γ⊢B≡A = tyEqWfCtx Γ⊢B≡A
...| TyEqTrans Γ⊢A≡B _ = tyEqWfCtx Γ⊢A≡B
...| TyEqPi _ Γ⊢A≡B _ = tyEqWfCtx Γ⊢A≡B
...| TyEqSubst _ Γ⇒Δ = sbEqWfCtx Γ⇒Δ
...| TyEqRussel Γ⊢A≡B∷U = tmEqWfCtx Γ⊢A≡B∷U
...| TyEqPiSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TyEqUSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TyEqSubstSubst _ _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TyEqSubstId Γ⊢A = tyWfCtx Γ⊢A

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmEqWfCtx tm with tm
...| TmEqRefl Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = tmEqWfCtx Γ⊢b≡a∷A
...| TmEqTrans Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqLam _ Γ◁A⊢a≡b∷B = proj₁ (ctxExtInversion (tmEqWfCtx Γ◁A⊢a≡b∷B))
...| TmEqApp _ _ Γ⊢a≡b∷A = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqPi _ Γ⊢A≡B∷U _ = tmEqWfCtx Γ⊢A≡B∷U
...| TmEqSubst _ Γ⊢γ₁≡γ₂⇒Δ = sbEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| TmEqConv Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqSubstId Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSubstVarExt _ Γ⊢γ◀a⇒Δ = sbWfCtx Γ⊢γ◀a⇒Δ
...| TmEqSubstVarDrop _ Γ⊢dropX⇒Δ = sbWfCtx Γ⊢dropX⇒Δ
...| TmEqLamSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqAppSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqSubstSubst _ Γ⊢γ⇒Δ _ = sbWfCtx Γ⊢γ⇒Δ
...| TmEqUSubst Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqPiSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqPiBeta _ _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqPiEta Γ⊢f∷PiAB = tmWfCtx Γ⊢f∷PiAB

-- sbEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ
sbEqWfCtx eq with eq
...| SbEqRefl Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = sbEqWfCtx Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = sbEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ _ _ = sbEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| SbEqComp _ Γ⇒Δ = sbEqWfCtx Γ⇒Δ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ _ = sbEqWfCtx Γ⊢γ₁≡γ₂⇒Δ₁
...| SbEqCompAssoc Ξ⇒Θ _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqIdₗ _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqIdᵣ _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqExtVar Γ⊢Var0∷A = tmWfCtx Γ⊢Var0∷A
...| SbEqDropExt _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqDropComp _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbEqExtComp _ Γ⇒Δ = sbWfCtx Γ⇒Δ