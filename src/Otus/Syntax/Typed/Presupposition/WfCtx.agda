{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.WfCtx where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Inversion

open Product

private
  variable
    Γ Δ  : Context
    γ γ₁ γ₂ : Substitution
    A B : Type
    f a b c : Term

tyWfCtx : Γ ⊢ A → ⊢ Γ
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
sbWfCtx : Γ ⊢ γ ⇒ Δ → ⊢ Γ

tyEqWfCtx : Γ ⊢ A ≡ⱼ B → ⊢ Γ
tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ
sbEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ

ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyWfCtx (tyJdg _ Γ⊢A∷Ul) = tmWfCtx Γ⊢A∷Ul

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmWfCtx tm with tm
...| TmVarᶻ Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A
...| TmVarˢ Γ⊢VarX∷A Γ⊢B = CExt (tmWfCtx Γ⊢VarX∷A) Γ⊢B
...| TmPi Γ⊢A∷U _ = tmWfCtx Γ⊢A∷U
...| TmLam _ Γ◁A⊢b∷B = proj₁ (ctxExtInversion (tmWfCtx Γ◁A⊢b∷B))
...| TmApp _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmNat ⊢Γ = ⊢Γ
...| TmZero ⊢Γ = ⊢Γ
...| TmSucc Γ⊢a∷Nat = tmWfCtx Γ⊢a∷Nat
...| TmNatElim _ _ _ Γ⊢c∷ℕ = tmWfCtx Γ⊢c∷ℕ
...| TmSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmUniv ⊢Γ = ⊢Γ
...| TmCum Γ⊢A∷Ul = tmWfCtx Γ⊢A∷Ul
...| TmTyConv Γ⊢a∷A _ = tmWfCtx Γ⊢a∷A

-- sbWfCtx : Γ ⊢ γ ⇒ Δ → ⊢ Γ
sbWfCtx sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⇒Δ Γ⊢A = CExt (sbWfCtx Γ⇒Δ) Γ⊢A
...| SbExt Γ⇒Δ _ _ = sbWfCtx Γ⇒Δ
...| SbComp _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| SbConv Γ⇒Δ₁ _ = sbWfCtx Γ⇒Δ₁

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyEqWfCtx (tyEqJdg _ Γ⊢A≡B∷Ul) = tmEqWfCtx Γ⊢A≡B∷Ul

-- tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ
tmEqWfCtx tm with tm
...| TmEqSym Γ⊢b≡a∷A = tmEqWfCtx Γ⊢b≡a∷A
...| TmEqTrans Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqLam _ Γ◁A⊢a≡b∷B = proj₁ (ctxExtInversion (tmEqWfCtx Γ◁A⊢a≡b∷B))
...| TmEqApp _ _ Γ⊢a≡b∷A = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqPi _ Γ⊢A≡B∷U _ = tmEqWfCtx Γ⊢A≡B∷U
...| TmEqSucc Γ⊢a≡b∷Nat = tmEqWfCtx Γ⊢a≡b∷Nat
...| TmEqNatElim _ _ _ _ Γ⊢c₁≡c₂∷Nat = tmEqWfCtx Γ⊢c₁≡c₂∷Nat
...| TmEqSubst _ Γ⊢γ₁≡γ₂⇒Δ = sbEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| TmEqCum Γ⊢A≡B∷Ul = tmEqWfCtx Γ⊢A≡B∷Ul
...| TmEqConv Γ⊢a≡b∷A _ = tmEqWfCtx Γ⊢a≡b∷A
...| TmEqSubstId Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqSubstVarExt _ Γ⊢γ◀a⇒Δ = sbWfCtx Γ⊢γ◀a⇒Δ
...| TmEqSubstVarDrop _ Γ⊢dropX⇒Δ = sbWfCtx Γ⊢dropX⇒Δ
...| TmEqLamSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqAppSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqNatSubst Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqZeroSubst Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqSuccSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqNatElimSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqSubstSubst _ _ Γ⊢γ⇒Δ = sbWfCtx Γ⊢γ⇒Δ
...| TmEqUSubst Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqPiSubst _ Γ⇒Δ = sbWfCtx Γ⇒Δ
...| TmEqPiBeta _ _ Γ⊢a∷A = tmWfCtx Γ⊢a∷A
...| TmEqNatElimZero _ Γ⊢a∷A _ = tmWfCtx Γ⊢a∷A
...| TmEqNatElimSucc _ Γ⊢a∷A _ _ = tmWfCtx Γ⊢a∷A
...| TmEqPiEta Γ⊢f∷PiAB = tmWfCtx Γ⊢f∷PiAB
...| TmEqNatEta Γ⊢c∷ℕ = tmWfCtx Γ⊢c∷ℕ

-- sbEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ
sbEqWfCtx eq with eq
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

-- ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWf CEqEmp = CEmp , CEmp
ctxEqWf (CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡ⱼΔ
  in CExt ⊢Γ Γ⊢A , CExt ⊢Δ Δ⊢B