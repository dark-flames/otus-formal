{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Heter.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Heter.Base


private
  variable
    Γ Δ Ξ : Context
    γ γ₁ γ₂ δ : Substitution
    A B C a b c : Term

hTmEqWeakenTy : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ A ≡ⱼ B
hTmEqWeakenTy (HTmEqₗ  Γ⊢A≡B _) = Γ⊢A≡B
hTmEqWeakenTy (HTmEqᵣ Γ⊢A≡B _) = Γ⊢A≡B

hTmEqWeakenₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ A
hTmEqWeakenₗ (HTmEqₗ  _ Γ⊢a≡b∷A) = Γ⊢a≡b∷A
hTmEqWeakenₗ (HTmEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = tmEqConv' Γ⊢a≡b∷B Γ⊢A≡B

hTmEqWeakenᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ B
hTmEqWeakenᵣ (HTmEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = tmEqConv Γ⊢a≡b∷A Γ⊢A≡B
hTmEqWeakenᵣ (HTmEqᵣ _ Γ⊢a≡b∷B) = Γ⊢a≡b∷B

hTmEqFund : Γ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
hTmEqFund Γ⊢A Γ⊢a≡b∷A = HTmEqₗ (TyEqRefl Γ⊢A) Γ⊢a≡b∷A

hTmEqFund' : Γ ⊢ A → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
hTmEqFund' Γ⊢A Γ⊢b≡a∷A = HTmEqₗ (TyEqRefl Γ⊢A) (TmEqSym Γ⊢b≡a∷A)

hTmEqFundTyₗ : Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hTmEqFundTyₗ Γ⊢a∷A Γ⊢A≡B = HTmEqₗ Γ⊢A≡B (TmEqRefl Γ⊢a∷A)

hTmEqFundTyᵣ : Γ ⊢ a ∷ B → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hTmEqFundTyᵣ Γ⊢a∷B Γ⊢A≡B = HTmEqᵣ Γ⊢A≡B(TmEqRefl Γ⊢a∷B)

hTmEqFundTyₗ' : Γ ⊢ a ∷ A → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hTmEqFundTyₗ' Γ⊢a∷A Γ⊢B≡A = HTmEqₗ (TyEqSym Γ⊢B≡A) (TmEqRefl Γ⊢a∷A)

hTmEqFundTyᵣ' : Γ ⊢ a ∷ B → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hTmEqFundTyᵣ' Γ⊢a∷B Γ⊢B≡A = HTmEqᵣ (TyEqSym Γ⊢B≡A) (TmEqRefl Γ⊢a∷B)

hTmEqCoeₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → (Γ ⊢ A ≡ⱼ B) × (Γ ⊢ a ≡ⱼ b ∷ A)
hTmEqCoeₗ Γ⊢a∷A≡b∷B = hTmEqWeakenTy Γ⊢a∷A≡b∷B , hTmEqWeakenₗ Γ⊢a∷A≡b∷B

hTmEqCoeᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → (Γ ⊢ A ≡ⱼ B) × (Γ ⊢ a ≡ⱼ b ∷ B)
hTmEqCoeᵣ Γ⊢a∷A≡b∷B = hTmEqWeakenTy Γ⊢a∷A≡b∷B , hTmEqWeakenᵣ Γ⊢a∷A≡b∷B

hTmEqRefl : Γ ⊢ A → Γ ⊢ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ A
hTmEqRefl Γ⊢A Γ⊢a∷A = HTmEqₗ (TyEqRefl Γ⊢A) (TmEqRefl Γ⊢a∷A)

hTmEqSym : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ a ∷ A
hTmEqSym (HTmEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = HTmEqᵣ (TyEqSym Γ⊢A≡B) (TmEqSym Γ⊢a≡b∷A)
hTmEqSym (HTmEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = HTmEqₗ (TyEqSym Γ⊢A≡B) (TmEqSym Γ⊢a≡b∷B) 

hTmEqTrans : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
hTmEqTrans Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷A = hTmEqCoeₗ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hTmEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C
    Γ⊢b≡c∷A = tmEqConv' Γ⊢b≡c∷B Γ⊢A≡B
  in HTmEqₗ Γ⊢A≡C (TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A)

hTmEqTransₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ B
hTmEqTransₗ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hTmEqCoeᵣ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hTmEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C 
  in HTmEqᵣ Γ⊢A≡B (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hTmEqTransᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
hTmEqTransᵣ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hTmEqCoeᵣ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hTmEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C 
  in HTmEqₗ Γ⊢B≡C (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hTmEqHomoTransₗ : Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
hTmEqHomoTransₗ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢B≡C , Γ⊢b≡c∷B = hTmEqCoeₗ Γ⊢b∷B≡c∷C
  in HTmEqₗ Γ⊢B≡C (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hTmEqHomoTransᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ≡ⱼ c ∷ B → Γ ⊢ a ∷ A ≡ⱼ c ∷ B
hTmEqHomoTransᵣ Γ⊢a∷A≡b∷B Γ⊢b≡c∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hTmEqCoeᵣ Γ⊢a∷A≡b∷B
  in HTmEqᵣ Γ⊢A≡B (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hTmEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Δ ⊢ a ∷ A ≡ⱼ b ∷ B
hTmEqStability ⊢Γ≡Δ (HTmEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = HTmEqₗ (tyEqStability ⊢Γ≡Δ Γ⊢A≡B) (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷A)
hTmEqStability ⊢Γ≡Δ (HTmEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = HTmEqᵣ (tyEqStability ⊢Γ≡Δ Γ⊢A≡B) (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷B)

hTmEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
hTmEqStability' ⊢Γ≡Δ (HTmEqₗ  Δ⊢A≡B Δ⊢a≡b∷A) = HTmEqₗ (tyEqStability' ⊢Γ≡Δ Δ⊢A≡B) (tmEqStability' ⊢Γ≡Δ Δ⊢a≡b∷A)
hTmEqStability' ⊢Γ≡Δ (HTmEqᵣ Δ⊢A≡B Δ⊢a≡b∷B) = HTmEqᵣ (tyEqStability' ⊢Γ≡Δ Δ⊢A≡B) (tmEqStability' ⊢Γ≡Δ Δ⊢a≡b∷B)

hTmEqConvₗ : Γ ⊢ A ≡ⱼ C → Γ ⊢ a ∷ A ≡ⱼ b ∷ B →  Γ ⊢ a ∷ C ≡ⱼ b ∷ B 
hTmEqConvₗ Γ⊢A≡C Γ⊢a∷A≡b∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷A = hTmEqCoeₗ Γ⊢a∷A≡b∷B
  in HTmEqₗ (TyEqTrans (TyEqSym Γ⊢A≡C) Γ⊢A≡B) (tmEqConv Γ⊢a≡b∷A Γ⊢A≡C)

hTmEqConvᵣ : Γ ⊢ B ≡ⱼ C → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ C 
hTmEqConvᵣ Γ⊢B≡C Γ⊢a∷A≡b∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hTmEqCoeᵣ Γ⊢a∷A≡b∷B
  in HTmEqᵣ (TyEqTrans Γ⊢A≡B Γ⊢B≡C) (tmEqConv Γ⊢a≡b∷B Γ⊢B≡C)

hTmEqSubst : Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ 
    → Γ ⊢ a [ γ₁ ]ₑ ∷ A [ γ₁ ]ₑ ≡ⱼ b [ γ₂ ]ₑ ∷ B [ γ₂ ]ₑ
hTmEqSubst Δ⊢a∷A≡b∷B Γ⊢γ₁≡γ₂⇒Δ = let
    Δ⊢A≡B , Δ⊢a≡b∷A = hTmEqCoeₗ Δ⊢a∷A≡b∷B
    Γ⊢A[γ₁]≡B[γ₂] = TyEqSubst Δ⊢A≡B Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢a[γ₁]≡b[γ₂]∷A[γ₁] = TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ
  in HTmEqₗ Γ⊢A[γ₁]≡B[γ₂] Γ⊢a[γ₁]≡b[γ₂]∷A[γ₁]

hTmEqSubst₁ : Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ γ ⇒ Δ 
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ ≡ⱼ b [ γ ]ₑ ∷ B [ γ ]ₑ
hTmEqSubst₁ Δ⊢a∷A≡b∷B Γ⊢γ⇒Δ = hTmEqSubst Δ⊢a∷A≡b∷B (SbEqRefl Γ⊢γ⇒Δ)

hTmEqSubst₂ : Δ ⊢ A → Δ ⊢ a ∷ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ 
    → Γ ⊢ a [ γ₁ ]ₑ ∷ A [ γ₁ ]ₑ ≡ⱼ a [ γ₂ ]ₑ ∷ A [ γ₂ ]ₑ
hTmEqSubst₂ Δ⊢A Δ⊢a∷A Γ⊢γ₁≡γ₂⇒Δ = hTmEqSubst (hTmEqRefl Δ⊢A Δ⊢a∷A) Γ⊢γ₁≡γ₂⇒Δ

hTmEqSubstSubst : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ A → Ξ ⊢ a ∷ A
    → Γ ⊢ a [ δ ]ₑ [ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ ≡ⱼ a [ δ ∘ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
hTmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A Ξ⊢a∷A = let 
    Γ⊢A[δ][γ]≡A[δ∘γ] = TyEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A
  in HTmEqₗ Γ⊢A[δ][γ]≡A[δ∘γ] (TmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A)