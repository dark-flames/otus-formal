{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.ContextConversion where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions

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

{-
Binary Logical Relation between Context
-}

data ⊢_≃_ : Context → Context → Set where
  CConvEmpty : ⊢ ε ≃ ε
  CConvExt :  ⊢ Γ ≃ Δ
      → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B
      → Δ ⊢ A → Δ ⊢ B → Δ ⊢ A ≡ⱼ B
      → ⊢ Γ , A ≃ Δ , B

ctxConvExtRefl : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A → ⊢ Γ , A ≃ Δ , A
ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A = CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢A (TyEqRefl Γ⊢A) Δ⊢A Δ⊢A (TyEqRefl Δ⊢A)

ctxConvRefl : ⊢ Γ → ⊢ Γ ≃ Γ
ctxConvRefl (CEmp) = CConvEmpty
ctxConvRefl (CExt ⊢Γ Γ⊢A) = let ⊢Γ≡Γ = ctxConvRefl ⊢Γ
  in ctxConvExtRefl ⊢Γ≡Γ Γ⊢A Γ⊢A

ctxConvSym : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Γ
ctxConvSym eq with eq
... | CConvEmpty = CConvEmpty
... | CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B = 
  CConvExt (ctxConvSym ⊢Γ≃Δ) Δ⊢B Δ⊢A (TyEqSym Δ⊢A≡B) Γ⊢B Γ⊢A (TyEqSym Γ⊢A≡B)

ctxConvWf : ⊢ Γ ≃ Δ → ⊢ Γ × ⊢ Δ
ctxConvWf CConvEmpty = pair CEmp CEmp
ctxConvWf (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = let pair ⊢Γ ⊢Δ = ctxConvWf ⊢Γ≃Δ
  in pair (CExt ⊢Γ Γ⊢A) (CExt ⊢Δ Δ⊢B)

weakenCtxConv : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Δ
weakenCtxConv CConvEmpty = CEqRefl CEmp
weakenCtxConv (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenCtxConv ⊢Γ≃Δ) Γ⊢A Δ⊢B Γ⊢A≡B

weakenCtxConv' : ⊢ Γ ≃ Δ → ⊢ Δ ≡ⱼ Γ
weakenCtxConv' CConvEmpty = CEqRefl CEmp
weakenCtxConv' (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenCtxConv' ⊢Γ≃Δ) Δ⊢B Γ⊢A (TyEqSym Δ⊢A≡B)


tyStability : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A
substStability : ⊢ Γ ≃ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
tmStability : ⊢ Γ ≃ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A

tyEqStability : ⊢ Γ ≃ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
substEqStability : ⊢ Γ ≃ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
tmEqStability : ⊢ Γ ≃ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A

-- tmStability : ⊢ Γ ≃ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability (CConvEmpty) = id
tmStability (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVar _) = let Δ,B⊢var∷B = TmVar Δ⊢B
    in let Δ,B⇒Δ = displayMap Δ⊢B
    in let Δ,B⊢B≡A = TyEqSubst (TyEqSym Δ⊢A≡B)  (SbEqRefl Δ,B⇒Δ)
    in TmTyConv Δ,B⊢var∷B Δ,B⊢B≡A
tmStability ⊢Γ≃Δ (TmLam Γ⊢A Γ,A⊢b∷B) = let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢b∷B = tmStability ⊢Γ,A≃Δ,A Γ,A⊢b∷B
    in TmLam Δ⊢A Δ,A⊢b∷B
tmStability ⊢Γ≃Δ (TmPi Γ⊢A∷U Γ,A⊢B∷U) = let Δ⊢A∷U = tmStability ⊢Γ≃Δ Γ⊢A∷U
    in let Δ⊢A = TyRussel Δ⊢A∷U
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ (TyRussel Γ⊢A∷U) Δ⊢A
    in let Δ,A⊢B∷U = tmStability ⊢Γ,A≃Δ,A Γ,A⊢B∷U 
    in TmPi Δ⊢A∷U Δ,A⊢B∷U
tmStability ⊢Γ≃Δ (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let Δ⊢f∷PiAB = tmStability ⊢Γ≃Δ Γ⊢f∷PiAB
    in let Δ⊢a∷A = tmStability ⊢Γ≃Δ Γ⊢a∷A
    in TmApp Δ⊢f∷PiAB Δ⊢a∷A
tmStability ⊢Γ≃Δ (TmSubst Ξ⊢a∷A Γ⊢γ⇒Ξ) = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmSubst Ξ⊢a∷A Δ⊢γ⇒Ξ
tmStability ⊢Γ≃Δ (TmU _) = TmU (proj₂ (ctxConvWf ⊢Γ≃Δ))
tmStability ⊢Γ≃Δ (TmTyConv Γ⊢a∷A Γ⊢A≡B) = let Δ⊢a∷A = tmStability ⊢Γ≃Δ Γ⊢a∷A 
    in let Δ⊢A≡B = tyEqStability ⊢Γ≃Δ Γ⊢A≡B
    in TmTyConv Δ⊢a∷A Δ⊢A≡B

-- substStability : ⊢ Γ ≃ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
substStability CConvEmpty = id
substStability (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (SbDropˢ Γ⇒Ξ _) = 
    let Δ⇒Ξ = substStability ⊢Γ≃Δ Γ⇒Ξ in SbDropˢ Δ⇒Ξ Δ⊢B
substStability ⊢Γ≃Δ (SbId ⊢Γ) = let ⊢Δ = proj₂ (ctxConvWf ⊢Γ≃Δ)
    in SbConv (SbId ⊢Δ) (weakenCtxConv' ⊢Γ≃Δ)
substStability ⊢Γ≃Δ (SbExt Γ⇒Ξ Ξ⊢A Γ⊢a∷Aγ) = let Δ⇒Ξ = substStability ⊢Γ≃Δ Γ⇒Ξ
    in let Δ⊢a∷Aγ = tmStability ⊢Γ≃Δ Γ⊢a∷Aγ
    in SbExt Δ⇒Ξ Ξ⊢A Δ⊢a∷Aγ
substStability ⊢Γ≃Δ (SbComp Γ₂⇒Γ₃ Γ⇒Γ₂) = let Δ⇒Γ₃ = substStability ⊢Γ≃Δ Γ⇒Γ₂
    in SbComp Γ₂⇒Γ₃ Δ⇒Γ₃
substStability ⊢Γ≃Δ (SbConv Γ⇒Ξ₁ ⊢Ξ₁≡Ξ₂) = let Δ⇒Ξ₁ = substStability ⊢Γ≃Δ Γ⇒Ξ₁
    in SbConv Δ⇒Ξ₁ ⊢Ξ₁≡Ξ₂

-- tyStability : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A
tyStability ⊢Γ≃Δ ty with ty
... | TyPi Γ⊢A Γ,A⊢B = let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢B = tyStability Γ,A≃Δ,A Γ,A⊢B
    in TyPi Δ⊢A Δ,A⊢B
... | TyU _ = let ⊢Δ = proj₂ (ctxConvWf ⊢Γ≃Δ)
    in TyU ⊢Δ
... | TySubst Ξ⊢A Γ⇒Ξ = let Δ⇒Ξ = substStability ⊢Γ≃Δ Γ⇒Ξ
    in TySubst Ξ⊢A Δ⇒Ξ
... | TyRussel Γ⊢A∷U = TyRussel (tmStability ⊢Γ≃Δ Γ⊢A∷U)


-- tyEqStability : ⊢ Γ ≃ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqStability ⊢Γ≃Δ eq with eq
... | TyEqRefl Γ⊢A = TyEqRefl (tyStability ⊢Γ≃Δ Γ⊢A)
... | TyEqSym Γ⊢B≡A = TyEqSym (tyEqStability ⊢Γ≃Δ Γ⊢B≡A)
... | TyEqTrans Γ⊢A≡B Γ⊢B≡C = TyEqTrans (tyEqStability ⊢Γ≃Δ Γ⊢A≡B) (tyEqStability ⊢Γ≃Δ Γ⊢B≡C)
... | TyEqPi Γ⊢A Γ⊢A≡B Γ,A⊢C≡D = let Δ⊢A≡B = tyEqStability ⊢Γ≃Δ Γ⊢A≡B -- todo: try remove Γ⊢A
    in let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢C≡D = tyEqStability ⊢Γ,A≃Δ,A Γ,A⊢C≡D
    in TyEqPi Δ⊢A Δ⊢A≡B Δ,A⊢C≡D
... | TyEqSubst Ξ⊢A≡B Γ⊢γ₁≡γ₂⇒Ξ = TyEqSubst Ξ⊢A≡B (substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ)
... | TyEqRussel Γ⊢A≡B∷U = TyEqRussel (tmEqStability ⊢Γ≃Δ Γ⊢A≡B∷U)
... | TyEqPiSubst Ξ⊢PiAB Γ⊢γ⇒Ξ = TyEqPiSubst Ξ⊢PiAB (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ)
... | TyEqUSubst Ξ⊢U Γ⊢γ⇒Ξ = TyEqUSubst Ξ⊢U (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ)
... | TyEqSubstSubst Ξ⊢Aδ  Γ⊢γ⇒Ξ = TyEqSubstSubst Ξ⊢Aδ (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ)
... | TyEqSubstId Γ⊢A = TyEqSubstId (tyStability ⊢Γ≃Δ Γ⊢A)

-- substEqStability : ⊢ Γ ≃ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
substEqStability  ⊢Γ≃Δ eq with eq
... | SbEqRefl Γ⊢γ⇒Ξ = SbEqRefl (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ)
... | SbEqSym Γ⊢γ₂≡γ₁⇒Ξ = SbEqSym (substEqStability ⊢Γ≃Δ Γ⊢γ₂≡γ₁⇒Ξ)
... | SbEqTrans Γ⊢γ₁≡γ₂⇒Ξ  Γ⊢γ₂≡γ₃⇒Ξ  = SbEqTrans (substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ) (substEqStability ⊢Γ≃Δ Γ⊢γ₂≡γ₃⇒Ξ)
... | SbEqExt Γ⊢γ₁≡γ₂⇒Ξ Ξ⊢A Γ⊢a≡b∷Aγ₁ = SbEqExt (substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ) Ξ⊢A (tmEqStability ⊢Γ≃Δ Γ⊢a≡b∷Aγ₁)
... | SbEqComp Ξ⊢δ₁≡δ₂⇒Θ Γ⊢γ₁≡γ₂⇒Ξ = SbEqComp Ξ⊢δ₁≡δ₂⇒Θ (substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ)
... | SbEqConv Γ⊢γ₁≡γ₂⇒Ξ₁ ⊢Ξ₁≡Ξ₂ = SbEqConv (substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ₁) ⊢Ξ₁≡Ξ₂
... | SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ₁)
... | SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ Γ⊢id⇒Ξ₁ = SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ (substStability ⊢Γ≃Δ Γ⊢id⇒Ξ₁)
... | SbEqIdₗ Ξ₁⊢id⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqIdₗ Ξ₁⊢id⇒Ξ₂ (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ₁)
... | SbEqExtVar Γ⊢drop,var⇒Ξ Γ⊢id⇒Ξ = SbEqExtVar (substStability ⊢Γ≃Δ Γ⊢drop,var⇒Ξ) (substStability ⊢Γ≃Δ Γ⊢id⇒Ξ)
... | SbEqDropExt Ξ⊢drop⇒Θ Γ⊢γ,a⇒Ξ = SbEqDropExt Ξ⊢drop⇒Θ (substStability ⊢Γ≃Δ Γ⊢γ,a⇒Ξ)
... | SbEqDropComp Ξ⊢drop⇒Θ Γ⊢id⇒Ξ = SbEqDropComp Ξ⊢drop⇒Θ (substStability ⊢Γ≃Δ Γ⊢id⇒Ξ)
... | SbEqExtComp Ξ⊢δ,a⇒Θ Γ⊢γ⇒Ξ = SbEqExtComp Ξ⊢δ,a⇒Θ (substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ)

-- tmEqStability : ⊢ Γ ≃ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
tmEqStability ⊢Γ≃Δ eq with eq
... | TmEqRefl Γ⊢a∷A = TmEqRefl (tmStability ⊢Γ≃Δ Γ⊢a∷A )
... | TmEqSym Γ⊢b≡a∷A = TmEqSym (tmEqStability ⊢Γ≃Δ Γ⊢b≡a∷A)
... | TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans (tmEqStability ⊢Γ≃Δ Γ⊢a≡b∷A) (tmEqStability ⊢Γ≃Δ Γ⊢b≡c∷A)
... | TmEqLam Γ⊢A Γ,A⊢a≡b∷B = let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢a≡b∷B = tmEqStability ⊢Γ,A≃Δ,A Γ,A⊢a≡b∷B
    in TmEqLam Δ⊢A Δ,A⊢a≡b∷B
... | TmEqPi Γ⊢A Γ⊢A≡B∷U Γ,A⊢C≡D∷U = let Δ⊢A≡B∷U = tmEqStability ⊢Γ≃Δ Γ⊢A≡B∷U
    in let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢C≡D∷U = tmEqStability ⊢Γ,A≃Δ,A Γ,A⊢C≡D∷U
    in TmEqPi Δ⊢A Δ⊢A≡B∷U Δ,A⊢C≡D∷U
... | TmEqApp Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let Δ⊢f≡g∷PiAB = tmEqStability ⊢Γ≃Δ Γ⊢f≡g∷PiAB
    in let Δ⊢a≡b∷A = tmEqStability ⊢Γ≃Δ Γ⊢a≡b∷A
    in TmEqApp Δ⊢f≡g∷PiAB Δ⊢a≡b∷A
... | TmEqSubst Ξ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Ξ = let Δ⊢γ₁≡γ₂⇒Ξ = substEqStability ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ
    in TmEqSubst Ξ⊢a≡b∷A Δ⊢γ₁≡γ₂⇒Ξ
... | TmEqConv Γ⊢A≡B Γ⊢a≡b∷A = let Δ⊢A≡B = tyEqStability ⊢Γ≃Δ Γ⊢A≡B
    in let Δ⊢a≡b∷A = tmEqStability ⊢Γ≃Δ Γ⊢a≡b∷A
    in TmEqConv Δ⊢A≡B Δ⊢a≡b∷A
... | TmEqSubstId Γ⊢a∷A = let Δ⊢a∷A = tmStability ⊢Γ≃Δ Γ⊢a∷A
    in TmEqSubstId Δ⊢a∷A
... | TmEqSubstVarExt Ξ⊢var0∷A Γ⊢γ,a⇒Ξ = let Δ⊢γ,a⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ,a⇒Ξ
    in TmEqSubstVarExt Ξ⊢var0∷A Δ⊢γ,a⇒Ξ
... | TmEqSubstVarDrop Ξ⊢varx∷A Γ⊢dropy⇒Ξ = let Δ⊢dropy⇒Ξ = substStability ⊢Γ≃Δ Γ⊢dropy⇒Ξ
    in TmEqSubstVarDrop Ξ⊢varx∷A Δ⊢dropy⇒Ξ
... | TmEqLamSubst Ξ⊢lama∷PiAB Γ⊢γ⇒Ξ = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmEqLamSubst Ξ⊢lama∷PiAB Δ⊢γ⇒Ξ
... | TmEqPiSubst Ξ⊢PiAB∷U Γ⊢γ⇒Ξ = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmEqPiSubst Ξ⊢PiAB∷U Δ⊢γ⇒Ξ
... | TmEqAppSubst Ξ⊢fa∷A Γ⊢γ⇒Ξ = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmEqAppSubst Ξ⊢fa∷A Δ⊢γ⇒Ξ
... | TmEqSubstComp Ξ⊢δ⇒Θ Γ⊢γ⇒Ξ Θ⊢a∷A = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmEqSubstComp Ξ⊢δ⇒Θ Δ⊢γ⇒Ξ Θ⊢a∷A
... | TmEqUSubst Γ⊢γ⇒Ξ = let Δ⊢γ⇒Ξ = substStability ⊢Γ≃Δ Γ⊢γ⇒Ξ
    in TmEqUSubst Δ⊢γ⇒Ξ
... | TmEqPiBeta Γ⊢A Γ,A⊢b∷B Γ⊢a∷A = let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A 
    in let ⊢Γ,A≃Δ,A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    in let Δ,A⊢b∷B = tmStability ⊢Γ,A≃Δ,A Γ,A⊢b∷B
    in let Δ⊢a∷A = tmStability ⊢Γ≃Δ Γ⊢a∷A
    in TmEqPiBeta Δ⊢A Δ,A⊢b∷B Δ⊢a∷A
... | TmEqPiEta Γ⊢f∷PiAB = let Δ⊢f∷PiAB = tmStability ⊢Γ≃Δ Γ⊢f∷PiAB
    in TmEqPiEta Δ⊢f∷PiAB

ctxConvFundamental : ⊢ Γ ≡ⱼ Δ → ⊢ Γ ≃ Δ
ctxConvFundamental (CEqRefl ⊢Γ) = ctxConvRefl ⊢Γ
ctxConvFundamental (CEqExt ⊢Γ≡Δ Γ⊢A Δ⊢B Γ⊢A≡B) = let ⊢Γ≃Δ = ctxConvFundamental ⊢Γ≡Δ
    in let ⊢Δ≃Γ = ctxConvSym ⊢Γ≃Δ
    in let Γ⊢B = tyStability ⊢Δ≃Γ Δ⊢B
    in let Δ⊢A = tyStability ⊢Γ≃Δ Γ⊢A
    in let Δ⊢A≡B = tyEqStability  ⊢Γ≃Δ Γ⊢A≡B
    in CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B

ctxConvTrans : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Ξ → ⊢ Γ ≃ Ξ
ctxConvTrans (CConvEmpty) ⊢ε≃Ξ = ⊢ε≃Ξ
ctxConvTrans (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (CConvExt ⊢Δ≃Ξ _ Δ⊢C Δ⊢B≡C Ξ⊢B Ξ⊢C Ξ⊢B≡C) = let ⊢Γ≃Ξ = ctxConvTrans ⊢Γ≃Δ ⊢Δ≃Ξ
    in let Γ⊢C = tyStability (ctxConvSym ⊢Γ≃Δ) Δ⊢C
    in let Ξ⊢A = tyStability ⊢Δ≃Ξ Δ⊢A
    in let Δ⊢A≡C = TyEqTrans Δ⊢A≡B Δ⊢B≡C
    in let Γ⊢A≡C = tyEqStability (ctxConvSym ⊢Γ≃Δ) Δ⊢A≡C 
    in let Ξ⊢A≡C = tyEqStability ⊢Δ≃Ξ Δ⊢A≡C
    in CConvExt ⊢Γ≃Ξ Γ⊢A Γ⊢C Γ⊢A≡C Ξ⊢A Ξ⊢C Ξ⊢A≡C

ctxEqStabilityₗ : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Ξ → ⊢ Δ ≡ⱼ Ξ
ctxEqStabilityₗ ⊢Γ≃Δ ⊢Γ≡Ξ = let ⊢Γ≃Ξ = ctxConvFundamental ⊢Γ≡Ξ
    in weakenCtxConv (ctxConvTrans (ctxConvSym ⊢Γ≃Δ) ⊢Γ≃Ξ)

ctxEqStabilityᵣ : ⊢ Γ ≃ Δ → ⊢ Ξ ≡ⱼ Γ → ⊢ Ξ ≡ⱼ Δ
ctxEqStabilityᵣ ⊢Γ≃Δ ⊢Ξ≡Γ = let ⊢Ξ≃Γ = ctxConvFundamental ⊢Ξ≡Γ
    in weakenCtxConv (ctxConvTrans ⊢Ξ≃Γ ⊢Γ≃Δ)