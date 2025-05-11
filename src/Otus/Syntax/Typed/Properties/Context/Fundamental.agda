{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Context.Fundamental where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context.Base

private
  variable
    x : ℕ
    Γ Δ Ξ  : Context
    γ γ₁ γ₂ δ : Substitution
    a b A B : Term

---- Theorems
ctxConvFundamental : ⊢ Γ ≡ⱼ Δ → ⊢ Γ ≃ Δ
weakenCtxConv : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Δ
weakenCtxConv' : ⊢ Γ ≃ Δ → ⊢ Δ ≡ⱼ Γ

ctxConvRefl : ⊢ Γ → ⊢ Γ ≃ Γ
ctxConvSym : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Γ
ctxConvTrans : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Ξ → ⊢ Γ ≃ Ξ

ctxConvWf : ⊢ Γ ≃ Δ → ⊢ Γ × ⊢ Δ

tyCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A
substCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
tmCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A

tyEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
substEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
tmEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
ctxEqCtxConvₗ : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Ξ → ⊢ Δ ≡ⱼ Ξ
ctxEqCtxConvᵣ : ⊢ Γ ≃ Δ → ⊢ Ξ ≡ⱼ Γ → ⊢ Ξ ≡ⱼ Δ

-- ⊢ Γ → ⊢ Γ ≃ Γ
ctxConvRefl (CEmp) = CConvEmpty
ctxConvRefl (CExt ⊢Γ Γ⊢A) = let ⊢Γ≡Γ = ctxConvRefl ⊢Γ
  in ctxConvExtRefl ⊢Γ≡Γ Γ⊢A Γ⊢A

-- ctxConvSym : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Γ
ctxConvSym eq with eq
...| CConvEmpty = CConvEmpty
...| CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B = 
  CConvExt (ctxConvSym ⊢Γ≃Δ) Δ⊢B Δ⊢A (TyEqSym Δ⊢A≡B) Γ⊢B Γ⊢A (TyEqSym Γ⊢A≡B)

-- ctxConvWf : ⊢ Γ ≃ Δ → ⊢ Γ × ⊢ Δ
ctxConvWf CConvEmpty = CEmp , CEmp
ctxConvWf (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = let
    ⊢Γ , ⊢Δ = ctxConvWf ⊢Γ≃Δ
  in CExt ⊢Γ Γ⊢A , CExt ⊢Δ Δ⊢B

-- weakenCtxConv : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Δ
weakenCtxConv CConvEmpty = CEqRefl CEmp
weakenCtxConv (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenCtxConv ⊢Γ≃Δ) Γ⊢A Γ⊢B Γ⊢A≡B

-- weakenCtxConv' : ⊢ Γ ≃ Δ → ⊢ Δ ≡ⱼ Γ
weakenCtxConv' CConvEmpty = CEqRefl CEmp
weakenCtxConv' (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenCtxConv' ⊢Γ≃Δ) Δ⊢B Δ⊢A (TyEqSym Δ⊢A≡B)


-- tmCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmCtxConv (CConvEmpty) = id
tmCtxConv (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarᶻ _) = let 
    Δ▷B⊢Var0∷B = TmVarᶻ Δ⊢B
    ⊢Δ = proj₂ (ctxConvWf ⊢Γ≃Δ)
    Δ▷B⇒Δ = SbDropˢ (SbId ⊢Δ) Δ⊢B
    Δ▷B⊢B≡A = tyEqSubst₁ (TyEqSym Δ⊢A≡B) Δ▷B⇒Δ
  in TmTyConv Δ▷B⊢Var0∷B Δ▷B⊢B≡A
tmCtxConv (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarˢ Γ⊢VarX∷C _) = let
    Δ⊢VarX∷C = tmCtxConv ⊢Γ≃Δ Γ⊢VarX∷C 
  in TmVarˢ Δ⊢VarX∷C Δ⊢B
tmCtxConv ⊢Γ≃Δ (TmLam Γ⊢A Γ▷A⊢b∷B) = let 
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢b∷B = tmCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢b∷B
  in TmLam Δ⊢A Δ▷A⊢b∷B
tmCtxConv ⊢Γ≃Δ (TmPi Γ⊢A∷U Γ▷A⊢B∷U) = let
    Δ⊢A∷U = tmCtxConv ⊢Γ≃Δ Γ⊢A∷U
    Δ⊢A = TyRussel Δ⊢A∷U
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ (TyRussel Γ⊢A∷U) Δ⊢A
    Δ▷A⊢B∷U = tmCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢B∷U 
  in TmPi Δ⊢A∷U Δ▷A⊢B∷U
tmCtxConv ⊢Γ≃Δ (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let
    Δ⊢f∷PiAB = tmCtxConv ⊢Γ≃Δ Γ⊢f∷PiAB
    Δ⊢a∷A = tmCtxConv ⊢Γ≃Δ Γ⊢a∷A
  in TmApp Δ⊢f∷PiAB Δ⊢a∷A
tmCtxConv ⊢Γ≃Δ (TmSubst Ξ⊢a∷A Γ⊢γ⇒Ξ) = let 
  Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmSubst Ξ⊢a∷A Δ⊢γ⇒Ξ
tmCtxConv ⊢Γ≃Δ (TmU _) = TmU (proj₂ (ctxConvWf ⊢Γ≃Δ))
tmCtxConv ⊢Γ≃Δ (TmTyConv Γ⊢a∷A Γ⊢A≡B) = let 
    Δ⊢a∷A = tmCtxConv ⊢Γ≃Δ Γ⊢a∷A 
    Δ⊢A≡B = tyEqCtxConv ⊢Γ≃Δ Γ⊢A≡B
  in TmTyConv Δ⊢a∷A Δ⊢A≡B

-- substCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
substCtxConv CConvEmpty = id
substCtxConv (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (SbDropˢ Γ⇒Ξ _) = 
  let Δ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⇒Ξ in SbDropˢ Δ⇒Ξ Δ⊢B
substCtxConv ⊢Γ≃Δ (SbId ⊢Γ) = let ⊢Δ = proj₂ (ctxConvWf ⊢Γ≃Δ)
  in SbConv (SbId ⊢Δ) (weakenCtxConv' ⊢Γ≃Δ)
substCtxConv ⊢Γ≃Δ (SbExt Γ⇒Ξ Ξ⊢A Γ⊢a∷Aγ) = let 
    Δ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⇒Ξ
    Δ⊢a∷Aγ = tmCtxConv ⊢Γ≃Δ Γ⊢a∷Aγ
  in SbExt Δ⇒Ξ Ξ⊢A Δ⊢a∷Aγ
substCtxConv ⊢Γ≃Δ (SbComp Γ₂⇒Γ₃ Γ⇒Γ₂) = let 
    Δ⇒Γ₃ = substCtxConv ⊢Γ≃Δ Γ⇒Γ₂
  in SbComp Γ₂⇒Γ₃ Δ⇒Γ₃
substCtxConv ⊢Γ≃Δ (SbConv Γ⇒Ξ₁ ⊢Ξ₁≡Ξ₂) = let 
    Δ⇒Ξ₁ = substCtxConv ⊢Γ≃Δ Γ⇒Ξ₁
  in SbConv Δ⇒Ξ₁ ⊢Ξ₁≡Ξ₂

-- tyCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A
tyCtxConv ⊢Γ≃Δ ty with ty
...| TyPi Γ⊢A Γ▷A⊢B = let 
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢B = tyCtxConv Γ▷A≃Δ▷A Γ▷A⊢B
  in TyPi Δ⊢A Δ▷A⊢B
...| TyU _ = let ⊢Δ = proj₂ (ctxConvWf ⊢Γ≃Δ)
  in TyU ⊢Δ
...| TySubst Ξ⊢A Γ⇒Ξ = let 
    Δ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⇒Ξ
  in TySubst Ξ⊢A Δ⇒Ξ
...| TyRussel Γ⊢A∷U = TyRussel (tmCtxConv ⊢Γ≃Δ Γ⊢A∷U)


-- tyEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqCtxConv ⊢Γ≃Δ eq with eq
...| TyEqRefl Γ⊢A = TyEqRefl (tyCtxConv ⊢Γ≃Δ Γ⊢A)
...| TyEqSym Γ⊢B≡A = TyEqSym (tyEqCtxConv ⊢Γ≃Δ Γ⊢B≡A)
...| TyEqTrans Γ⊢A≡B Γ⊢B≡C = TyEqTrans (tyEqCtxConv ⊢Γ≃Δ Γ⊢A≡B) (tyEqCtxConv ⊢Γ≃Δ Γ⊢B≡C)
...| TyEqPi Γ⊢A Γ⊢A≡B Γ▷A⊢C≡D = let 
    Δ⊢A≡B = tyEqCtxConv ⊢Γ≃Δ Γ⊢A≡B -- todo: try remove Γ⊢A
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢C≡D = tyEqCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢C≡D
  in TyEqPi Δ⊢A Δ⊢A≡B Δ▷A⊢C≡D
...| TyEqSubst Ξ⊢A≡B Γ⊢γ₁≡γ₂⇒Ξ = TyEqSubst Ξ⊢A≡B (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ)
...| TyEqRussel Γ⊢A≡B∷U = TyEqRussel (tmEqCtxConv ⊢Γ≃Δ Γ⊢A≡B∷U)
...| TyEqPiSubst Ξ⊢PiAB Γ⊢γ⇒Ξ = TyEqPiSubst Ξ⊢PiAB (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ)
...| TyEqUSubst Ξ⊢U Γ⊢γ⇒Ξ = TyEqUSubst Ξ⊢U (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ)
...| TyEqSubstSubst Ξ⊢δ⇒Θ Γ⊢γ⇒Ξ Θ⊢A = TyEqSubstSubst Ξ⊢δ⇒Θ (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ) Θ⊢A
...| TyEqSubstId Γ⊢A = TyEqSubstId (tyCtxConv ⊢Γ≃Δ Γ⊢A)

-- substEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
substEqCtxConv  ⊢Γ≃Δ eq with eq
...| SbEqRefl Γ⊢γ⇒Ξ = SbEqRefl (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ)
...| SbEqSym Γ⊢γ₂≡γ₁⇒Ξ = SbEqSym (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₂≡γ₁⇒Ξ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Ξ  Γ⊢γ₂≡γ₃⇒Ξ  = SbEqTrans (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ) (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₂≡γ₃⇒Ξ)
...| SbEqExt Γ⊢γ₁≡γ₂⇒Ξ Ξ⊢A Γ⊢a≡b∷Aγ₁ = SbEqExt (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ) Ξ⊢A (tmEqCtxConv ⊢Γ≃Δ Γ⊢a≡b∷Aγ₁)
...| SbEqComp Ξ⊢δ₁≡δ₂⇒Θ Γ⊢γ₁≡γ₂⇒Ξ = SbEqComp Ξ⊢δ₁≡δ₂⇒Θ (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ)
...| SbEqConv Γ⊢γ₁≡γ₂⇒Ξ₁ ⊢Ξ₁≡Ξ₂ = SbEqConv (substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ₁) ⊢Ξ₁≡Ξ₂
...| SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ₁)
...| SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ Γ⊢id⇒Ξ₁ = SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ (substCtxConv ⊢Γ≃Δ Γ⊢id⇒Ξ₁)
...| SbEqIdₗ Ξ₁⊢id⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqIdₗ Ξ₁⊢id⇒Ξ₂ (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ₁)
...| SbEqExtVar Γ⊢drop▶var⇒Ξ Γ⊢id⇒Ξ = SbEqExtVar (substCtxConv ⊢Γ≃Δ Γ⊢drop▶var⇒Ξ) (substCtxConv ⊢Γ≃Δ Γ⊢id⇒Ξ)
...| SbEqDropExt Ξ⊢drop⇒Θ Γ⊢γ▶a⇒Ξ = SbEqDropExt Ξ⊢drop⇒Θ (substCtxConv ⊢Γ≃Δ Γ⊢γ▶a⇒Ξ)
...| SbEqDropComp Ξ⊢dropX⇒Θ Γ⊢drop1⇒Ξ = SbEqDropComp Ξ⊢dropX⇒Θ (substCtxConv ⊢Γ≃Δ Γ⊢drop1⇒Ξ)
...| SbEqExtComp Ξ⊢δ▶a⇒Θ Γ⊢γ⇒Ξ = SbEqExtComp Ξ⊢δ▶a⇒Θ (substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ)

-- tmEqCtxConv : ⊢ Γ ≃ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
tmEqCtxConv ⊢Γ≃Δ eq with eq
...| TmEqRefl Γ⊢a∷A = TmEqRefl (tmCtxConv ⊢Γ≃Δ Γ⊢a∷A )
...| TmEqSym Γ⊢b≡a∷A = TmEqSym (tmEqCtxConv ⊢Γ≃Δ Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans (tmEqCtxConv ⊢Γ≃Δ Γ⊢a≡b∷A) (tmEqCtxConv ⊢Γ≃Δ Γ⊢b≡c∷A)
...| TmEqLam Γ⊢A Γ▷A⊢a≡b∷B = let 
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢a≡b∷B = tmEqCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢a≡b∷B
  in TmEqLam Δ⊢A Δ▷A⊢a≡b∷B
...| TmEqPi Γ⊢A Γ⊢A≡B∷U Γ▷A⊢C≡D∷U = let 
    Δ⊢A≡B∷U = tmEqCtxConv ⊢Γ≃Δ Γ⊢A≡B∷U
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢C≡D∷U = tmEqCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢C≡D∷U
  in TmEqPi Δ⊢A Δ⊢A≡B∷U Δ▷A⊢C≡D∷U
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    Δ⊢f≡g∷PiAB = tmEqCtxConv ⊢Γ≃Δ Γ⊢f≡g∷PiAB
    Δ⊢a≡b∷A = tmEqCtxConv ⊢Γ≃Δ Γ⊢a≡b∷A
    Δ⊢PiAB = tyCtxConv ⊢Γ≃Δ Γ⊢PiAB
  in TmEqApp Δ⊢PiAB Δ⊢f≡g∷PiAB Δ⊢a≡b∷A
...| TmEqSubst Ξ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Ξ = let 
    Δ⊢γ₁≡γ₂⇒Ξ = substEqCtxConv ⊢Γ≃Δ Γ⊢γ₁≡γ₂⇒Ξ
  in TmEqSubst Ξ⊢a≡b∷A Δ⊢γ₁≡γ₂⇒Ξ
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let 
    Δ⊢A≡B = tyEqCtxConv ⊢Γ≃Δ Γ⊢A≡B
    Δ⊢a≡b∷A = tmEqCtxConv ⊢Γ≃Δ Γ⊢a≡b∷A
  in TmEqConv Δ⊢a≡b∷A Δ⊢A≡B
...| TmEqSubstId Γ⊢a∷A = let 
    Δ⊢a∷A = tmCtxConv ⊢Γ≃Δ Γ⊢a∷A
  in TmEqSubstId Δ⊢a∷A
...| TmEqSubstVarExt Ξ⊢Var0∷A Γ⊢γ▶a⇒Ξ = let 
    Δ⊢γ▶a⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ▶a⇒Ξ
  in TmEqSubstVarExt Ξ⊢Var0∷A Δ⊢γ▶a⇒Ξ
...| TmEqSubstVarDrop Ξ⊢VarX∷A Γ⊢dropy⇒Ξ = let 
    Δ⊢dropy⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢dropy⇒Ξ
  in TmEqSubstVarDrop Ξ⊢VarX∷A Δ⊢dropy⇒Ξ
...| TmEqLamSubst Ξ⊢lama∷PiAB Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmEqLamSubst Ξ⊢lama∷PiAB Δ⊢γ⇒Ξ
...| TmEqPiSubst Ξ⊢PiAB∷U Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmEqPiSubst Ξ⊢PiAB∷U Δ⊢γ⇒Ξ
...| TmEqAppSubst Ξ⊢fa∷A Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmEqAppSubst Ξ⊢fa∷A Δ⊢γ⇒Ξ
...| TmEqSubstSubst Ξ⊢δ⇒Θ Γ⊢γ⇒Ξ Θ⊢a∷A = let 
    Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmEqSubstSubst Ξ⊢δ⇒Θ Δ⊢γ⇒Ξ Θ⊢a∷A
...| TmEqUSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = substCtxConv ⊢Γ≃Δ Γ⊢γ⇒Ξ
  in TmEqUSubst Δ⊢γ⇒Ξ
...| TmEqPiBeta Γ⊢A Γ▷A⊢b∷B Γ⊢a∷A = let 
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A 
    ⊢Γ▷A≃Δ▷A = ctxConvExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A
    Δ▷A⊢b∷B = tmCtxConv ⊢Γ▷A≃Δ▷A Γ▷A⊢b∷B
    Δ⊢a∷A = tmCtxConv ⊢Γ≃Δ Γ⊢a∷A
  in TmEqPiBeta Δ⊢A Δ▷A⊢b∷B Δ⊢a∷A
...| TmEqPiEta Γ⊢f∷PiAB = let 
    Δ⊢f∷PiAB = tmCtxConv ⊢Γ≃Δ Γ⊢f∷PiAB
  in TmEqPiEta Δ⊢f∷PiAB

-- ctxConvFundamental : ⊢ Γ ≡ⱼ Δ → ⊢ Γ ≃ Δ
ctxConvFundamental (CEqRefl ⊢Γ) = ctxConvRefl ⊢Γ
ctxConvFundamental (CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B) = let 
    ⊢Γ≃Δ = ctxConvFundamental ⊢Γ≡Δ
    Δ⊢A = tyCtxConv ⊢Γ≃Δ Γ⊢A
    Δ⊢B = tyCtxConv ⊢Γ≃Δ Γ⊢B
    Δ⊢A≡B = tyEqCtxConv  ⊢Γ≃Δ Γ⊢A≡B
  in CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B

-- ctxConvTrans : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Ξ → ⊢ Γ ≃ Ξ
ctxConvTrans (CConvEmpty) ⊢ε≃Ξ = ⊢ε≃Ξ
ctxConvTrans (CConvExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (CConvExt ⊢Δ≃Ξ _ Δ⊢C Δ⊢B≡C Ξ⊢B Ξ⊢C Ξ⊢B≡C) = let 
    ⊢Γ≃Ξ = ctxConvTrans ⊢Γ≃Δ ⊢Δ≃Ξ
    Γ⊢C = tyCtxConv (ctxConvSym ⊢Γ≃Δ) Δ⊢C
    Ξ⊢A = tyCtxConv ⊢Δ≃Ξ Δ⊢A
    Δ⊢A≡C = TyEqTrans Δ⊢A≡B Δ⊢B≡C
    Γ⊢A≡C = tyEqCtxConv (ctxConvSym ⊢Γ≃Δ) Δ⊢A≡C 
    Ξ⊢A≡C = tyEqCtxConv ⊢Δ≃Ξ Δ⊢A≡C
  in CConvExt ⊢Γ≃Ξ Γ⊢A Γ⊢C Γ⊢A≡C Ξ⊢A Ξ⊢C Ξ⊢A≡C

-- ctxEqCtxConvₗ : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Ξ → ⊢ Δ ≡ⱼ Ξ

ctxEqCtxConvₗ ⊢Γ≃Δ ⊢Γ≡Ξ = let ⊢Γ≃Ξ = ctxConvFundamental ⊢Γ≡Ξ
  in weakenCtxConv (ctxConvTrans (ctxConvSym ⊢Γ≃Δ) ⊢Γ≃Ξ)

-- ctxEqCtxConvᵣ : ⊢ Γ ≃ Δ → ⊢ Ξ ≡ⱼ Γ → ⊢ Ξ ≡ⱼ Δ
ctxEqCtxConvᵣ ⊢Γ≃Δ ⊢Ξ≡Γ = let ⊢Ξ≃Γ = ctxConvFundamental ⊢Ξ≡Γ
  in weakenCtxConv (ctxConvTrans ⊢Ξ≃Γ ⊢Γ≃Δ)