{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Presuppositions where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; J)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term

ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
tyWfCtx : Γ ⊢ A → ⊢ Γ
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ

substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ × ⊢ Δ
tyEqWfCtx : Γ ⊢ A ≡ⱼ B → ⊢ Γ
tmEqWfCtx : Γ ⊢ a ≡ⱼ b ∷ A → ⊢ Γ

ctxExtExp : ⊢ Γ , A → ⊢ Γ × Γ ⊢ A
ctxExtExp (CExt ⊢Γ Γ⊢A) = pair ⊢Γ Γ⊢A

ctxExt : Γ ⊢ A → ⊢ Γ , A
ctxExt Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A

-- substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
substWfCtx sb with sb
...| (SbId ⊢Γ) = pair ⊢Γ ⊢Γ
...| (SbDropˢ Γ⇒Δ Γ⊢A) = let pair ⊢Γ ⊢Δ = substWfCtx Γ⇒Δ
  in pair (CExt ⊢Γ Γ⊢A) ⊢Δ
...| (SbExt Γ⇒Δ Δ⊢A Γ⊢a∷Aγ) = let pair ⊢Γ ⊢Δ = substWfCtx Γ⇒Δ
  in let ⊢Δ,A = (CExt ⊢Δ Δ⊢A)
  in pair ⊢Γ ⊢Δ,A
...| (SbComp Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))
...| (SbConv Γ⇒Δ₁ ⊢Δ₁≡Δ₂) = pair (proj₁ (substWfCtx Γ⇒Δ₁)) (proj₂ (ctxEqWf ⊢Δ₁≡Δ₂))


-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyWfCtx ty with ty
...| (TyPi Γ⊢A Γ,A⊢B) = tyWfCtx Γ⊢A 
...| (TyU ⊢Γ) = ⊢Γ
...| (TySubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TyRussel Γ⊢A∷U) = tmWfCtx Γ⊢A∷U

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmWfCtx tm with tm
...| (TmVar Γ⊢A) = ctxExt Γ⊢A
...| (TmLam _ Γ,A⊢b∷B) = proj₁ (ctxExtExp (tmWfCtx Γ,A⊢b∷B))
...| (TmPi Γ⊢A∷U _) = tmWfCtx Γ⊢A∷U
...| (TmApp _ Γ⊢a∷A) = tmWfCtx Γ⊢a∷A
...| (TmSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TmU ⊢Γ) = ⊢Γ
...| (TmTyConv Γ⊢a∷A _) = tmWfCtx Γ⊢a∷A

-- 

-- ctxEqWf : ⊢ Γ ≡ⱼ Δ → ⊢ Γ × ⊢ Δ
ctxEqWf eq with eq
...| (CEqRefl ⊢Γ) = pair ⊢Γ ⊢Γ
...| (CEqExt ⊢Γ≡Δ Γ⊢A Δ⊢B _) = let pair ⊢Γ ⊢Δ = ctxEqWf ⊢Γ≡Δ
  in pair (CExt ⊢Γ Γ⊢A) (CExt ⊢Δ Δ⊢B)

-- substEqWfCtx : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Γ × ⊢ Δ
substEqWfCtx eq with eq
...| (SbEqRefl Γ⇒Δ) = substWfCtx Γ⇒Δ
...| (SbEqSym Γ⊢γ₂≡γ₁⇒Δ) = substEqWfCtx Γ⊢γ₂≡γ₁⇒Δ
...| (SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _) = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
...| (SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A _) = let pair ⊢Γ ⊢Δ = substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ
  in pair ⊢Γ (CExt ⊢Δ Δ⊢A)
...| (SbEqComp Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substEqWfCtx Γ⇒Δ)) (proj₂ (substEqWfCtx Δ⇒Ξ))
...| (SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂) = pair (proj₁ (substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ₁)) (proj₂ (ctxEqWf ⊢Δ₁≡Δ₂))
...| (SbEqCompAssoc Ξ⇒Θ _ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Ξ⇒Θ))
...| (SbEqIdₗ Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))
...| (SbEqIdᵣ Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))
...| (SbEqExtVar Γ⇒Δ _) = substWfCtx Γ⇒Δ
...| (SbEqDropExt Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))
...| (SbEqDropComp Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))
...| (SbEqExtComp Δ⇒Ξ Γ⇒Δ) = pair (proj₁ (substWfCtx Γ⇒Δ)) (proj₂ (substWfCtx Δ⇒Ξ))

-- tyWfCtx : Γ ⊢ A → ⊢ Γ
tyEqWfCtx ty with ty
...| (TyEqRefl Γ⊢A) = tyWfCtx Γ⊢A
...| (TyEqSym Γ⊢B≡A) = tyEqWfCtx Γ⊢B≡A
...| (TyEqTrans Γ⊢A≡B Γ⊢B≡C) = tyEqWfCtx Γ⊢A≡B
...| (TyEqPi Γ⊢A Γ⊢A≡B Γ,A⊢C≡D) = tyEqWfCtx Γ⊢A≡B
...| (TyEqSubst _ Γ⇒Δ) = proj₁ (substEqWfCtx Γ⇒Δ)
...| (TyEqRussel Γ⊢A≡B∷U) = tmEqWfCtx Γ⊢A≡B∷U
...| (TyEqPiSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TyEqUSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TyEqSubstSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TyEqSubstId Γ⊢A) = tyWfCtx Γ⊢A

-- tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ
tmEqWfCtx tm with tm
...| (TmEqRefl Γ⊢a∷A) = tmWfCtx Γ⊢a∷A
...| (TmEqSym Γ⊢b≡a∷A) = tmEqWfCtx Γ⊢b≡a∷A
...| (TmEqTrans Γ⊢a≡b∷A _) = tmEqWfCtx Γ⊢a≡b∷A
...| (TmEqLam Γ⊢A Γ,A⊢a≡b∷B) = tyWfCtx Γ⊢A -- proj₁ (ctxExtExp (tmEqWfCtx Γ,A⊢a≡b∷B))
...| (TmEqApp _ Γ⊢a≡b∷A) = tmEqWfCtx Γ⊢a≡b∷A
...| (TmEqPi Γ⊢A Γ⊢A≡B∷U _) = tmEqWfCtx Γ⊢A≡B∷U
...| (TmEqSubst _ Γ⊢γ₁≡γ₂⇒Δ) = proj₁ (substEqWfCtx Γ⊢γ₁≡γ₂⇒Δ)
...| (TmEqConv _ Γ⊢a≡b∷A) = tmEqWfCtx Γ⊢a≡b∷A
...| (TmEqSubstId Γ⊢a∷A) = tmWfCtx Γ⊢a∷A
...| (TmEqSubstVarExt _ Γ⊢γ,a⇒Δ) = proj₁ (substWfCtx Γ⊢γ,a⇒Δ)
...| (TmEqSubstVarDrop _ Γ⊢dropX⇒Δ) = proj₁ (substWfCtx Γ⊢dropX⇒Δ)
...| (TmEqLamSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TmEqAppSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TmEqSubstComp _ Γ⊢γ⇒Δ _) = proj₁ (substWfCtx Γ⊢γ⇒Δ)
...| (TmEqUSubst Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TmEqPiSubst _ Γ⇒Δ) = proj₁ (substWfCtx Γ⇒Δ)
...| (TmEqPiBeta _ _ Γ⊢a∷A) = tmWfCtx Γ⊢a∷A
...| (TmEqPiEta Γ⊢f∷PiAB) = tmWfCtx Γ⊢f∷PiAB
