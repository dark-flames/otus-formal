{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Heterogeneous where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context


private
  variable
    l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    A B C a b c : Term


-- Heterogeneous term equality
infix 4 _⊢_∷_≡ⱼ_∷_
data _⊢_∷_≡ⱼ_∷_ : Context → Term → Term → Term → Term → Set where
    HEqₗ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
    HEqᵣ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B

hEqWeakenTy : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ A ≡ⱼ B
hEqWeakenTy (HEqₗ  Γ⊢A≡B _) = Γ⊢A≡B
hEqWeakenTy (HEqᵣ Γ⊢A≡B _) = Γ⊢A≡B


hEqWeakenₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ A
hEqWeakenₗ (HEqₗ  _ Γ⊢a≡b∷A) = Γ⊢a≡b∷A
hEqWeakenₗ (HEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = tmEqConv' Γ⊢a≡b∷B Γ⊢A≡B

hEqWeakenᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ B
hEqWeakenᵣ (HEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = tmEqConv Γ⊢a≡b∷A Γ⊢A≡B
hEqWeakenᵣ (HEqᵣ _ Γ⊢a≡b∷B) = Γ⊢a≡b∷B

hEqCoeₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → (Γ ⊢ A ≡ⱼ B) × (Γ ⊢ a ≡ⱼ b ∷ A)
hEqCoeₗ Γ⊢a∷A≡b∷B = hEqWeakenTy Γ⊢a∷A≡b∷B , hEqWeakenₗ Γ⊢a∷A≡b∷B

hEqCoeᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → (Γ ⊢ A ≡ⱼ B) × (Γ ⊢ a ≡ⱼ b ∷ B)
hEqCoeᵣ Γ⊢a∷A≡b∷B = hEqWeakenTy Γ⊢a∷A≡b∷B , hEqWeakenᵣ Γ⊢a∷A≡b∷B

hEqRefl : Γ ⊢ A → Γ ⊢ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ A
hEqRefl Γ⊢A Γ⊢a∷A = HEqₗ (TyEqRefl Γ⊢A) (TmEqRefl Γ⊢a∷A)

hEqFund : Γ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
hEqFund Γ⊢A Γ⊢a≡b∷A = HEqₗ (TyEqRefl Γ⊢A) Γ⊢a≡b∷A

hEqFund' : Γ ⊢ A → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
hEqFund' Γ⊢A Γ⊢b≡a∷A = HEqₗ (TyEqRefl Γ⊢A) (TmEqSym Γ⊢b≡a∷A)

hEqTyEqₗ : Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hEqTyEqₗ Γ⊢a∷A Γ⊢A≡B = HEqₗ Γ⊢A≡B (TmEqRefl Γ⊢a∷A)

hEqTyEqᵣ : Γ ⊢ a ∷ B → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hEqTyEqᵣ Γ⊢a∷B Γ⊢A≡B = HEqᵣ Γ⊢A≡B(TmEqRefl Γ⊢a∷B)

hEqTyEqₗ' : Γ ⊢ a ∷ A → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hEqTyEqₗ' Γ⊢a∷A Γ⊢B≡A = HEqₗ (TyEqSym Γ⊢B≡A) (TmEqRefl Γ⊢a∷A)

hEqTyEqᵣ' : Γ ⊢ a ∷ B → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
hEqTyEqᵣ' Γ⊢a∷B Γ⊢B≡A = HEqᵣ (TyEqSym Γ⊢B≡A) (TmEqRefl Γ⊢a∷B)

hEqConvₗ : Γ ⊢ A ≡ⱼ C → Γ ⊢ a ∷ A ≡ⱼ b ∷ B →  Γ ⊢ a ∷ C ≡ⱼ b ∷ B 
hEqConvₗ Γ⊢A≡C Γ⊢a∷A≡b∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷A = hEqCoeₗ Γ⊢a∷A≡b∷B
  in HEqₗ (TyEqTrans (TyEqSym Γ⊢A≡C) Γ⊢A≡B) (tmEqConv Γ⊢a≡b∷A Γ⊢A≡C)

hEqConvᵣ : Γ ⊢ B ≡ⱼ C → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ C 
hEqConvᵣ Γ⊢B≡C Γ⊢a∷A≡b∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hEqCoeᵣ Γ⊢a∷A≡b∷B
  in HEqᵣ (TyEqTrans Γ⊢A≡B Γ⊢B≡C) (tmEqConv Γ⊢a≡b∷B Γ⊢B≡C)


hEqSym : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ a ∷ A
hEqSym (HEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = HEqᵣ (TyEqSym Γ⊢A≡B) (TmEqSym Γ⊢a≡b∷A)
hEqSym (HEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = HEqₗ (TyEqSym Γ⊢A≡B) (TmEqSym Γ⊢a≡b∷B) 

hEqTrans : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
hEqTrans Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷A = hEqCoeₗ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C
    Γ⊢b≡c∷A = tmEqConv' Γ⊢b≡c∷B Γ⊢A≡B
  in HEqₗ Γ⊢A≡C (TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A)

hEqTransₗ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ B
hEqTransₗ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hEqCoeᵣ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C 
  in HEqᵣ Γ⊢A≡B (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hEqTransᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
hEqTransᵣ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hEqCoeᵣ Γ⊢a∷A≡b∷B
    Γ⊢B≡C , Γ⊢b≡c∷B = hEqCoeₗ Γ⊢b∷B≡c∷C
    Γ⊢A≡C = TyEqTrans Γ⊢A≡B Γ⊢B≡C 
  in HEqₗ Γ⊢B≡C (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hEqHomoTransₗ : Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
hEqHomoTransₗ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C = let
    Γ⊢B≡C , Γ⊢b≡c∷B = hEqCoeₗ Γ⊢b∷B≡c∷C
  in HEqₗ Γ⊢B≡C (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hEqHomoTransᵣ : Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ≡ⱼ c ∷ B → Γ ⊢ a ∷ A ≡ⱼ c ∷ B
hEqHomoTransᵣ Γ⊢a∷A≡b∷B Γ⊢b≡c∷B = let
    Γ⊢A≡B , Γ⊢a≡b∷B = hEqCoeᵣ Γ⊢a∷A≡b∷B
  in HEqᵣ Γ⊢A≡B (TmEqTrans Γ⊢a≡b∷B Γ⊢b≡c∷B)

hEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Δ ⊢ a ∷ A ≡ⱼ b ∷ B
hEqStability ⊢Γ≡Δ (HEqₗ  Γ⊢A≡B Γ⊢a≡b∷A) = HEqₗ (tyEqStability ⊢Γ≡Δ Γ⊢A≡B) (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷A)
hEqStability ⊢Γ≡Δ (HEqᵣ Γ⊢A≡B Γ⊢a≡b∷B) = HEqᵣ (tyEqStability ⊢Γ≡Δ Γ⊢A≡B) (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷B)

hEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
hEqStability' ⊢Γ≡Δ (HEqₗ  Δ⊢A≡B Δ⊢a≡b∷A) = HEqₗ (tyEqStability' ⊢Γ≡Δ Δ⊢A≡B) (tmEqStability' ⊢Γ≡Δ Δ⊢a≡b∷A)
hEqStability' ⊢Γ≡Δ (HEqᵣ Δ⊢A≡B Δ⊢a≡b∷B) = HEqᵣ (tyEqStability' ⊢Γ≡Δ Δ⊢A≡B) (tmEqStability' ⊢Γ≡Δ Δ⊢a≡b∷B)

hEqSubst : Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ 
    → Γ ⊢ a [ γ₁ ]ₑ ∷ A [ γ₁ ]ₑ ≡ⱼ b [ γ₂ ]ₑ ∷ B [ γ₂ ]ₑ
hEqSubst Δ⊢a∷A≡b∷B Γ⊢γ₁≡γ₂⇒Δ = let
    Δ⊢A≡B , Δ⊢a≡b∷A = hEqCoeₗ Δ⊢a∷A≡b∷B
    Γ⊢A[γ₁]≡B[γ₂] = TyEqSubst Δ⊢A≡B Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢a[γ₁]≡b[γ₂]∷A[γ₁] = TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ
  in HEqₗ Γ⊢A[γ₁]≡B[γ₂] Γ⊢a[γ₁]≡b[γ₂]∷A[γ₁]

hEqSubst₁ : Δ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ γ ⇒ Δ 
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ ≡ⱼ b [ γ ]ₑ ∷ B [ γ ]ₑ
hEqSubst₁ Δ⊢a∷A≡b∷B Γ⊢γ⇒Δ = hEqSubst Δ⊢a∷A≡b∷B (SbEqRefl Γ⊢γ⇒Δ)

hEqSubst₂ : Δ ⊢ A → Δ ⊢ a ∷ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ 
    → Γ ⊢ a [ γ₁ ]ₑ ∷ A [ γ₁ ]ₑ ≡ⱼ a [ γ₂ ]ₑ ∷ A [ γ₂ ]ₑ
hEqSubst₂ Δ⊢A Δ⊢a∷A Γ⊢γ₁≡γ₂⇒Δ = hEqSubst (hEqRefl Δ⊢A Δ⊢a∷A) Γ⊢γ₁≡γ₂⇒Δ

hEqSubstSubst : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ A → Ξ ⊢ a ∷ A
    → Γ ⊢ a [ δ ]ₑ [ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ ≡ⱼ a [ δ ∘ γ ]ₑ ∷ A [ δ ∘ γ ]ₑ
hEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A Ξ⊢a∷A = let 
    Γ⊢A[δ][γ]≡A[δ∘γ] = TyEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢A
  in HEqₗ Γ⊢A[δ][γ]≡A[δ∘γ] (TmEqSubstSubst Δ⊢δ⇒Ξ Γ⊢γ⇒Δ Ξ⊢a∷A)