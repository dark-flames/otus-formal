{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.DefEq where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion
open import Otus.Syntax.Typed.Properties.Substitution

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; J)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term



tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A

substEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ
tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B

postulate
  tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A

-- tmWfTy : Γ ⊢ a ∷ A → Γ ⊢ A
tmWfTy tm with tm
...| (TmVar Γ⊢A) = let Γ,A⊢drop1⇒Γ = displayMap Γ⊢A
  in TySubst Γ⊢A Γ,A⊢drop1⇒Γ
...| (TmLam Γ⊢A Γ,A⊢b∷B) = TyPi Γ⊢A (tmWfTy Γ,A⊢b∷B )
...| (TmPi Γ⊢A∷U Γ,A⊢B∷U) = TyU (tmWfCtx Γ⊢A∷U)
...| (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let Γ⊢PiAB = tmWfTy Γ⊢f∷PiAB
  in let pair Γ⊢A Γ,A⊢B = piTyInversion Γ⊢PiAB
  in let Γ⊢id,a⇒Γ,A = section Γ⊢A Γ⊢a∷A
  in TySubst Γ,A⊢B Γ⊢id,a⇒Γ,A
...| (TmSubst Δ⊢a∷A Γ⇒Δ) = let Δ⊢A = tmWfTy Δ⊢a∷A
  in TySubst Δ⊢A Γ⇒Δ
...| (TmU ⊢Γ) = TyU ⊢Γ
...| (TmTyConv _ Γ⊢A≡B) = proj₂ (tyEqWf Γ⊢A≡B)

-- substEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ
substEqWf {Γ}{γ₁} {γ₂} {Δ} eq with eq
...| SbEqRefl Γ⇒Δ = pair Γ⇒Δ Γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = swap (substEqWf Γ⊢γ₂≡γ₁⇒Δ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ Γ⊢γ₂≡γ₃⇒Δ  = pair (proj₁ (substEqWf Γ⊢γ₁≡γ₂⇒Δ)) (proj₂ (substEqWf Γ⊢γ₂≡γ₃⇒Δ))
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a≡b∷Aγ₁ = let Γ⊢Aγ₁≡Aγ₂ = TyEqSubst (TyEqRefl Δ⊢A) Γ⊢γ₁≡γ₂⇒Δ
  in let pair Γ⊢γ₁⇒Δ Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in let pair Γ⊢a∷Aγ₁ Γ⊢b∷Aγ₁ = tmEqWf Γ⊢a≡b∷Aγ₁
  in let Γ⊢b∷Aγ₂ = TmTyConv Γ⊢b∷Aγ₁ Γ⊢Aγ₁≡Aγ₂
  in pair (SbExt Γ⊢γ₁⇒Δ Δ⊢A Γ⊢a∷Aγ₁) (SbExt Γ⊢γ₂⇒Δ Δ⊢A Γ⊢b∷Aγ₂)
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = let pair Δ⊢δ₁⇒Ξ Δ⊢δ₂⇒Ξ = substEqWf Δ⊢δ₁≡δ₂⇒Ξ
  in let pair Γ⊢γ₁⇒Δ Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in pair (SbComp Δ⊢δ₁⇒Ξ Γ⊢γ₁⇒Δ) (SbComp Δ⊢δ₂⇒Ξ Γ⊢γ₂⇒Δ)
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = let pair Γ⊢γ₁⇒Δ₁ Γ⊢γ₂⇒Δ₁ = substEqWf Γ⊢γ₁≡γ₂⇒Δ₁
  in pair (SbConv Γ⊢γ₁⇒Δ₁ ⊢Δ₁≡Δ₂) (SbConv Γ⊢γ₂⇒Δ₁ ⊢Δ₁≡Δ₂)
...| SbEqCompAssoc Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let Γ⊢ξ∘δ∘γ⇒Θ = SbComp (SbComp Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
  in let Γ⊢ξ∘[δ∘γ]⇒Θ = SbComp Ξ⊢ξ⇒Θ  (SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ)
  in pair Γ⊢ξ∘δ∘γ⇒Θ Γ⊢ξ∘[δ∘γ]⇒Θ
...| SbEqIdₗ Δ⊢id⇒Ξ Γ⊢γ⇒Δ = let ⊢Δ≡Ξ = idInversion Δ⊢id⇒Ξ
  in let Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ ⊢Δ≡Ξ
  in let Γ⊢id∘γ⇒Ξ = SbComp Δ⊢id⇒Ξ Γ⊢γ⇒Δ
  in pair Γ⊢id∘γ⇒Ξ Γ⊢γ⇒Ξ
...| SbEqIdᵣ Δ⊢γ⇒Ξ Γ⊢id⇒Δ = let ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in let Γ⊢γ⇒Ξ = substStability' ⊢Γ≡Δ Δ⊢γ⇒Ξ
  in let Γ⊢γ∘id⇒Ξ = SbComp Δ⊢γ⇒Ξ Γ⊢id⇒Δ 
  in pair Γ⊢γ∘id⇒Ξ Γ⊢γ⇒Ξ
...| SbEqExtVar Γ⊢drop,var⇒Δ Γ⊢id⇒Δ = pair Γ⊢drop,var⇒Δ Γ⊢id⇒Δ
...| SbEqDropExt Δ⊢drop1⇒Ξ Γ⊢γ,a⇒Δ = let Γ⊢drop1∘[γ,a]⇒Ξ = SbComp Δ⊢drop1⇒Ξ Γ⊢γ,a⇒Δ
  in let pair (ctxExtInv _ _ Δ'⊢A ⊢Δ≡Δ',A) (pair Γ⊢γ⇒Δ' Γ⊢a∷Aγ) = substExtInversion Γ⊢γ,a⇒Δ
  in let pair (ctxExtInv _ _ Δ''⊢A ⊢Δ≡Δ'',A) (⊢Δ''≡Ξ) = drop1Inversion Δ⊢drop1⇒Ξ
  in let ⊢Δ',A≡Δ'',A = ctxEqTrans (ctxEqSym ⊢Δ≡Δ',A) ⊢Δ≡Δ'',A
  in let ⊢Δ'≡Δ'' = proj₁ (ctxEqExtInversion ⊢Δ',A≡Δ'',A)
  in let ⊢Δ'≡Ξ = ctxEqTrans ⊢Δ'≡Δ'' ⊢Δ''≡Ξ
  in let Γ⊢γ⇒Ξ = SbConv Γ⊢γ⇒Δ' ⊢Δ'≡Ξ
  in pair Γ⊢drop1∘[γ,a]⇒Ξ Γ⊢γ⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ = let Γ⊢dropX∘drop1⇒Ξ = SbComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ
  in let pair (ctxExtInv _ _ Γ'⊢A ⊢Γ≡Γ',A) ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
  in let Γ'⊢dropX⇒Ξ = substStability' ⊢Γ'≡Δ Δ⊢dropX⇒Ξ
  in let Γ',A⊢dropSX⇒Ξ = SbDropˢ Γ'⊢dropX⇒Ξ Γ'⊢A
  in let Γ⊢dropSX⇒Ξ = substStability' ⊢Γ≡Γ',A Γ',A⊢dropSX⇒Ξ
  in pair Γ⊢dropX∘drop1⇒Ξ Γ⊢dropSX⇒Ξ
...| SbEqExtComp Δ⊢δ,a⇒Ξ Γ⊢γ⇒Δ = let Γ⊢[δ,a]∘γ⇒Ξ = SbComp Δ⊢δ,a⇒Ξ Γ⊢γ⇒Δ
  in let pair (ctxExtInv _ _ Ξ'⊢A ⊢Ξ≡Ξ',A) (pair Δ⊢δ⇒Ξ' Δ⊢a∷Aδ) = substExtInversion Δ⊢δ,a⇒Ξ
  in let Γ⊢δ∘γ⇒Ξ' = SbComp Δ⊢δ⇒Ξ' Γ⊢γ⇒Δ
  in let Γ⊢aγ∷Aδγ = TmSubst Δ⊢a∷Aδ Γ⊢γ⇒Δ
  in let Γ⊢Aδγ≡A[δ∘γ] = TyEqSubstSubst Δ⊢δ⇒Ξ' Γ⊢γ⇒Δ Ξ'⊢A
  in let Γ⊢aγ∷A[δ∘γ] = TmTyConv Γ⊢aγ∷Aδγ Γ⊢Aδγ≡A[δ∘γ]
  in let Γ⊢[δ∘γ],aγ⇒Ξ',A = SbExt Γ⊢δ∘γ⇒Ξ' Ξ'⊢A Γ⊢aγ∷A[δ∘γ]
  in let Γ⊢[δ∘γ],aγ⇒Ξ = SbConv Γ⊢[δ∘γ],aγ⇒Ξ',A (ctxEqSym ⊢Ξ≡Ξ',A)
  in pair Γ⊢[δ,a]∘γ⇒Ξ Γ⊢[δ∘γ],aγ⇒Ξ

-- tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
tyEqWf eq with eq
...| TyEqRefl Γ⊢A = pair Γ⊢A Γ⊢A
...| TyEqSym Γ⊢B≡A = swap (tyEqWf Γ⊢B≡A)
...| TyEqTrans Γ⊢A≡B Γ⊢B≡C = pair (proj₁ (tyEqWf Γ⊢A≡B)) (proj₂ (tyEqWf Γ⊢B≡C))
...| TyEqPi Γ⊢A Γ⊢A≡B Γ,A⊢C≡D = let Γ⊢B = proj₂ (tyEqWf Γ⊢A≡B)
  in let pair Γ,A⊢C Γ,A⊢D = tyEqWf Γ,A⊢C≡D
  in let ⊢Γ = tyWfCtx Γ⊢A
  in let ⊢Γ,A≡Γ,B = CEqExt (CEqRefl ⊢Γ) Γ⊢A Γ⊢B Γ⊢A≡B
  in let Γ,B⊢D = tyStability ⊢Γ,A≡Γ,B Γ,A⊢D
  in pair (TyPi Γ⊢A Γ,A⊢C) (TyPi Γ⊢B Γ,B⊢D)
...| TyEqSubst Δ⊢A≡B Γ⊢γ₁≡γ₂⇒Δ = let pair Δ⊢A Δ⊢B = tyEqWf Δ⊢A≡B
  in let pair Γ⊢γ₁⇒Δ Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
  in pair (TySubst Δ⊢A Γ⊢γ₁⇒Δ) (TySubst Δ⊢B Γ⊢γ₂⇒Δ)
...| TyEqRussel Γ⊢A≡B∷U = let pair Γ⊢A∷U Γ⊢B∷U = tmEqWf Γ⊢A≡B∷U
  in pair (TyRussel Γ⊢A∷U) (TyRussel Γ⊢B∷U)
...| TyEqPiSubst Δ⊢PiAB Γ⊢γ⇒Δ = let pair Δ⊢A Δ,A⊢B = piTyInversion Δ⊢PiAB
  in let Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
  in let Γ,Aγ⊢↑γ⇒Δ,A = liftSubst Γ⊢γ⇒Δ Δ⊢A
  in let Γ,Aγ⊢B[↑γ] = TySubst Δ,A⊢B Γ,Aγ⊢↑γ⇒Δ,A
  in pair (TySubst Δ⊢PiAB Γ⊢γ⇒Δ) (TyPi Γ⊢Aγ Γ,Aγ⊢B[↑γ])
...| TyEqUSubst Δ⊢U Γ⊢γ⇒Δ = let pair ⊢Γ ⊢Δ = substWfCtx Γ⊢γ⇒Δ
  in pair (TySubst (TyU ⊢Δ) Γ⊢γ⇒Δ) (TyU ⊢Γ)
...| TyEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A  = let Γ⊢Aδγ = TySubst (TySubst Ξ⊢A Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ 
  in let Γ⊢δ∘γ⇒Ξ = SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ
  in let Γ⊢A[δ∘γ] = TySubst Ξ⊢A Γ⊢δ∘γ⇒Ξ
  in pair Γ⊢Aδγ Γ⊢A[δ∘γ]
...| TyEqSubstId Γ⊢A = let ⊢Γ = tyWfCtx Γ⊢A
  in pair (TySubst Γ⊢A (SbId ⊢Γ)) (Γ⊢A)

tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A
tmEqWf eq with eq
...| TmEqRefl Γ⊢a∷A = pair Γ⊢a∷A Γ⊢a∷A
...| TmEqSym Γ⊢b≡a∷A = swap (tmEqWf Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = pair (proj₁ (tmEqWf Γ⊢a≡b∷A)) (proj₂ (tmEqWf Γ⊢b≡c∷A))
