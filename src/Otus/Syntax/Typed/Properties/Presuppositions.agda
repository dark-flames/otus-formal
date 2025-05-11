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

-- ctxEqWfCtx : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ
tyWfCtx : Γ ⊢ A → ⊢ Γ
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ

substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ
tyEqWfCtx : Γ ⊢ A ≡ⱼ B → ⊢ Γ
tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ

-- substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ
substWfCtx sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⇒Δ Γ⊢A = CExt (substWfCtx Γ⇒Δ) Γ⊢A
...| SbExt Γ⇒Δ _ _ = substWfCtx Γ⇒Δ
...| SbComp _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbConv Γ⇒Δ₁ _ = substWfCtx Γ⇒Δ₁


-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyWfCtx ty with ty
...| TyPi Γ⊢A Γ▷A⊢B = tyWfCtx Γ⊢A 
...| TyU ⊢Γ = ⊢Γ
...| TySubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TyRussel Γ⊢A∷U = tmWfCtx Γ⊢A∷U

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmWfCtx tm with tm
...| TmVarᶻ Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = CExt (tmWfCtx Γ⊢VarX∷A) Γ⊢B
...| TmLam _ Γ▷A⊢b∷B = proj₁ (ctxExtInversion (tmWfCtx Γ▷A⊢b∷B))
...| TmPi Γ⊢A∷U _ = tmWfCtx Γ⊢A∷U
...| TmApp _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TmU ⊢Γ = ⊢Γ
...| TmTyConv Γ⊢a∷A _ = tmWfCtx Γ⊢a∷A


-- substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ × ⊢ Δ
substEqWfCtx eq with eq
...| SbEqRefl Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = substEqWfCtx Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ _ _ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| SbEqComp _ Γ⇒Δ = substEqWfCtx Γ⇒Δ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ _ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ₁
...| SbEqCompAssoc Ξ⇒Θ _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqIdₗ _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqIdᵣ _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqExtVar Γ⇒Δ _ = substWfCtx Γ⇒Δ
...| SbEqDropExt _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqDropComp _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| SbEqExtComp _ Γ⇒Δ = substWfCtx Γ⇒Δ

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyEqWfCtx ty with ty
...| TyEqRefl Γ⊢A = tyWfCtx Γ⊢A
...| TyEqSym Γ⊢B≡A = tyEqWfCtx Γ⊢B≡A
...| TyEqTrans Γ⊢A≡B _ = tyEqWfCtx Γ⊢A≡B
...| TyEqPi _ Γ⊢A≡B _ = tyEqWfCtx Γ⊢A≡B
...| TyEqSubst _ Γ⇒Δ = substEqWfCtx Γ⇒Δ
...| TyEqRussel Γ⊢A≡B∷U = tmEqWfCtx Γ⊢A≡B∷U
...| TyEqPiSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TyEqUSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TyEqSubstSubst _ Γ⇒Δ _ = substWfCtx Γ⇒Δ
...| TyEqSubstId Γ⊢A = tyWfCtx Γ⊢A

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmEqWfCtx tm with tm
...| TmEqRefl Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = tmEqWfCtx Γ⊢b≡a∷A
...| TmEqTrans Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqLam _ Γ▷A⊢a≡b∷B = proj₁ (ctxExtInversion (tmEqWfCtx Γ▷A⊢a≡b∷B))
...| TmEqApp _ _ Γ⊢a≡b∷A = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqPi _ Γ⊢A≡B∷U _ = tmEqWfCtx Γ⊢A≡B∷U
...| TmEqSubst _ Γ⊢γ₁≡γ₂⇒Δ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| TmEqConv Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqSubstId Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSubstVarExt _ Γ⊢γ▶a⇒Δ = substWfCtx Γ⊢γ▶a⇒Δ
...| TmEqSubstVarDrop _ Γ⊢dropX⇒Δ = substWfCtx Γ⊢dropX⇒Δ
...| TmEqLamSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TmEqAppSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TmEqSubstSubst _ Γ⊢γ⇒Δ _ = substWfCtx Γ⊢γ⇒Δ
...| TmEqUSubst Γ⇒Δ = substWfCtx Γ⇒Δ
...| TmEqPiSubst _ Γ⇒Δ = substWfCtx Γ⇒Δ
...| TmEqPiBeta _ _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqPiEta Γ⊢f∷PiAB = tmWfCtx Γ⊢f∷PiAB
