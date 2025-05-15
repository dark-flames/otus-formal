{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ : Context
    γ : Substitution
    A B C : Term
    f a b c : Term


-- tactics

Tm-Varᶻ : Γ ⊢ A
    → Γ ▷ A ⊢ Var 0 ∷ A [ drop 1 ]ₑ
Tm-Varᶻ = TmVarᶻ

Tm-Varˢ : Γ ⊢ Var x ∷ A × Γ ⊢ B
    → Γ ▷ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
Tm-Varˢ = uncurry TmVarˢ

Tm-Var-ext : Γ ⊢ B → Γ ⊢ Var x ∷ A
    → Γ ▷ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
Tm-Var-ext Γ⊢B Γ⊢Var-x∷A = TmVarˢ Γ⊢Var-x∷A Γ⊢B

Tm-Lam : (Γ ⊢ A) × (Γ ▷ A ⊢ b ∷ B)
    → Γ ⊢ Lam b ∷ Pi A B
Tm-Lam  = uncurry TmLam

Tm-Lam-abs : Γ ⊢ A → Γ ▷ A ⊢ b ∷ B
    → Γ ⊢ Lam b ∷ Pi A B
Tm-Lam-abs  = TmLam

Tm-Pi : Γ ⊢ A ∷ U l₁ × Γ ▷ A ⊢ B ∷ U l₂
    → Γ ⊢ Pi A B ∷ U (l₁ ⊔ l₂)
Tm-Pi = uncurry TmPi

Tm-App : Γ ⊢ f ∷ Pi A B × Γ ⊢ a ∷ A
    → Γ ⊢ f ∙ a ∷ B [ idₛ ▶ a ]ₑ
Tm-App = uncurry TmApp

Tm-App-on : Γ ⊢ a ∷ A → Γ ⊢ f ∷ Pi A B
    → Γ ⊢ f ∙ a ∷ B [ idₛ ▶ a ]ₑ
Tm-App-on Γ⊢a∷A Γ⊢f∷PiAB = TmApp Γ⊢f∷PiAB Γ⊢a∷A

Tm-Subst : Δ ⊢ a ∷ A × Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst = uncurry TmSubst

Tm-Subst-by : Γ ⊢ γ ⇒ Δ → Δ ⊢ a ∷ A
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst-by Γ⊢γ⇒Δ Δ⊢a∷A = TmSubst Δ⊢a∷A Γ⊢γ⇒Δ

Tm-Subst-on : Δ ⊢ a ∷ A → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
Tm-Subst-on = TmSubst

Tm-U : ⊢ Γ 
    → Γ ⊢ U l ∷ U (lsuc l) 
Tm-U = TmU

Tm-TyConv : Γ ⊢ a ∷ A × Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ∷ B
Tm-TyConv = uncurry TmTyConv

Tm-TyConv-by : Γ ⊢ A ≡ⱼ B →  Γ ⊢ a ∷ A
    → Γ ⊢ a ∷ B
Tm-TyConv-by Γ⊢A≡B Γ⊢a∷A = tmTyConv Γ⊢a∷A Γ⊢A≡B

Tm-TyConv-by' : Γ ⊢ B ≡ⱼ A →  Γ ⊢ a ∷ A
    → Γ ⊢ a ∷ B
Tm-TyConv-by' Γ⊢B≡A Γ⊢a∷A = tmTyConv' Γ⊢a∷A Γ⊢B≡A 

Tm-Stability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A
    → Δ ⊢ a ∷ A
Tm-Stability = tmStability

Tm-Stability' : ⊢ Δ ≡ⱼ Γ → Γ ⊢ a ∷ A
    → Δ ⊢ a ∷ A
Tm-Stability' = tmStability'

module TmEqReasoning where
  infix 1 _⊢begin-tm_

  _⊢begin-tm_ : (Γ : Context) →  Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  Γ ⊢begin-tm aRb = aRb

  infixr 2 tm-step-≡-⟩  tm-step-≡-∣ tm-step-≡-⟨

  tm-step-≡-⟩ : (a : Term) → Γ ⊢ a ≡ⱼ b ∷ A  → Γ ⊢ b ≡ⱼ c ∷ A → Γ ⊢ a ≡ⱼ c ∷ A
  tm-step-≡-⟩ _ = TmEqTrans

  tm-step-≡-∣ : (a : Term) → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  tm-step-≡-∣ _ aRb = aRb

  tm-step-≡-⟨ : (a : Term) → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ b ≡ⱼ c ∷ A → Γ ⊢ a ≡ⱼ c ∷ A
  tm-step-≡-⟨ _ bRa bRc = TmEqTrans (TmEqSym bRa) bRc

  syntax tm-step-≡-⟩ x xRy yRz  = x tm-≡⟨ xRy ⟩ yRz
  syntax tm-step-≡-∣ x xRy      = x tm-≡⟨⟩ xRy
  syntax tm-step-≡-⟨ x yRx yRz  = x tm-≡⟨ yRx ⟨ yRz
  
  infix 3 tm-step-≡-⟨-∎ tm-step-≡-⟩-∎
  
  tm-step-≡-⟨-∎ : ∀ {Γ} → (a b : Term) → (A : Term) → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  tm-step-≡-⟨-∎ _ _ _ aRb = aRb

  tm-step-≡-⟩-∎ : ∀ {Γ} → (a b : Term) → (A : Term) → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  tm-step-≡-⟩-∎ _ _ _ bRa = TmEqSym bRa

  syntax tm-step-≡-⟨-∎ x y A xRy = x tm-≡⟨ xRy ⟩∣ y ∎∷ A
  syntax tm-step-≡-⟩-∎ x y A yRx = x tm-≡⟨ yRx ⟨∣ y ∎∷ A

module TmHEqReasoning where
  open import Otus.Syntax.Typed.Properties.Heter

  infix 1 _⊢begin-heq_ _⊢begin-heqₗ_ _⊢begin-heqᵣ_

  _⊢begin-heq_ : (Γ : Context) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
  Γ ⊢begin-heq Γ⊢a∷A≡b∷B = Γ⊢a∷A≡b∷B

  _⊢begin-heqₗ_ : (Γ : Context) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ A
  Γ ⊢begin-heqₗ Γ⊢a∷A≡b∷B = hTmEqWeakenₗ Γ⊢a∷A≡b∷B

  _⊢begin-heqᵣ_ : (Γ : Context) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ B
  Γ ⊢begin-heqᵣ Γ⊢a∷A≡b∷B = hTmEqWeakenᵣ Γ⊢a∷A≡b∷B

  infixr 2 homo-step-≡-⟩ homo-step-≡-⟨ 
  infixr 2 heter-step-≡-∣ heter-stepₗ-≡-⟩ heter-stepₗ-≡-⟨ heter-stepᵣ-≡-⟩ heter-stepᵣ-≡-⟨
  infixr 2 conv-step-≡-⟩ conv-step-≡-⟨

  homo-step-≡-⟩ : (a B : Term) → Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  homo-step-≡-⟩ _ _ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C = hTmEqHomoTransₗ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C
  homo-step-≡-⟨ : (a B : Term) → Γ ⊢ b ≡ⱼ a ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  homo-step-≡-⟨ _ _ Γ⊢b≡a∷B Γ⊢b∷B≡c∷C = hTmEqHomoTransₗ (TmEqSym Γ⊢b≡a∷B) Γ⊢b∷B≡c∷C

  heter-step-≡-∣ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
  heter-step-≡-∣ _ _ Γ⊢a∷A≡b∷B = Γ⊢a∷A≡b∷B
  -- by heter
  heter-stepₗ-≡-⟩ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
  heter-stepₗ-≡-⟩ _ _ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = hTmEqTrans Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C

  heter-stepₗ-≡-⟨ : (a A : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
  heter-stepₗ-≡-⟨ _ _ Γ⊢b∷B≡a∷A Γ⊢b∷B≡c∷C = hTmEqTrans (hTmEqSym Γ⊢b∷B≡a∷A) Γ⊢b∷B≡c∷C

  heter-stepᵣ-≡-⟩ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  heter-stepᵣ-≡-⟩ _ _ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = hTmEqTransᵣ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C

  heter-stepᵣ-≡-⟨ : (a A : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  heter-stepᵣ-≡-⟨ _ _ Γ⊢b∷B≡a∷A Γ⊢b∷B≡c∷C = hTmEqTransᵣ (hTmEqSym Γ⊢b∷B≡a∷A) Γ⊢b∷B≡c∷C

  conv-step-≡-⟩ : (a A : Term) → Γ ⊢ A ≡ⱼ C → Γ ⊢ a ∷ C ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
  conv-step-≡-⟩ _ _ Γ⊢A≡C Γ⊢a∷C≡b∷B = hTmEqConvₗ (TyEqSym Γ⊢A≡C) Γ⊢a∷C≡b∷B 

  conv-step-≡-⟨ : (a A : Term) → Γ ⊢ C ≡ⱼ A → Γ ⊢ a ∷ C ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
  conv-step-≡-⟨ _ _ Γ⊢C≡A Γ⊢a∷C≡b∷B = hTmEqConvₗ Γ⊢C≡A Γ⊢a∷C≡b∷B 

  syntax homo-step-≡-⟩ x X x≡y y≡z     = x ∷ X heq-≡⟨ x≡y ⟩ y≡z
  syntax homo-step-≡-⟨ x y≡x y≡z       = x ∷ X heq-≡⟨ y≡x ⟨ y≡z
  syntax heter-step-≡-∣ x X x≡y        = x ∷ X heq-≡⟨⟩ x≡y
  syntax heter-stepₗ-≡-⟩ x X x≡y y≡z    = x ∷ X heq-≡⟨∣ x≡y ∙⟩ y≡z
  syntax heter-stepₗ-≡-⟨ x X y≡x y≡z    = x ∷ X heq-≡⟨∣ y≡x ∙⟨ y≡z
  syntax heter-stepᵣ-≡-⟩ x X x≡y y≡z   = x ∷ X heq-≡⟨∙ x≡y ∣⟩ y≡z
  syntax heter-stepᵣ-≡-⟨ x X y≡x y≡z   = x ∷ X heq-≡⟨∙ y≡x ∣⟨ y≡z
  syntax conv-step-≡-⟩ x X X≡Y x≡z     = x ∷ X heq-≡⟨∷ X≡Y ∷⟩ x≡z
  syntax conv-step-≡-⟨ x X Y≡X x≡z     = x ∷ X heq-≡⟨∷ Y≡X ∷⟨ x≡z


  infixr 3 heter-step-≡-⟩-∎ heter-step-≡-⟨-∎
  infixr 3 homo-step-≡-⟩-∎ homo-step-≡-⟨-∎
  infixr 3 conv-step-≡-⟩-A∎ conv-step-≡-⟨-A∎ conv-step-≡-⟩-B∎ conv-step-≡-⟨-B∎

  homo-step-≡-⟩-∎ : (a b A B : Term) → Γ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
  homo-step-≡-⟩-∎ _ _ _ _ = hTmEqFund
  
  homo-step-≡-⟨-∎ : (a b A B : Term) → Γ ⊢ A → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
  homo-step-≡-⟨-∎ _ _ _ _ = hTmEqFund' 

  heter-step-≡-⟩-∎ : (a b A B : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B 
  heter-step-≡-⟩-∎ _ _ _ _ Γ⊢a∷A≡b∷B = Γ⊢a∷A≡b∷B

  heter-step-≡-⟨-∎ : (a b A B : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ B 
  heter-step-≡-⟨-∎ _ _ _ _ Γ⊢b∷B≡a∷A = hTmEqSym Γ⊢b∷B≡a∷A

  conv-step-≡-⟩-A∎ : (a A B : Term) → Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
  conv-step-≡-⟩-A∎ _ _ _ = hTmEqFundTyₗ

  conv-step-≡-⟩-B∎ : (a A B : Term) → Γ ⊢ a ∷ B → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
  conv-step-≡-⟩-B∎ _ _ _ = hTmEqFundTyᵣ

  conv-step-≡-⟨-A∎ : (a A B : Term) → Γ ⊢ a ∷ A → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
  conv-step-≡-⟨-A∎ _ _ _ = hTmEqFundTyₗ'

  conv-step-≡-⟨-B∎ : (a A B : Term) → Γ ⊢ a ∷ B → Γ ⊢ B ≡ⱼ A → Γ ⊢ a ∷ A ≡ⱼ a ∷ B
  conv-step-≡-⟨-B∎ _ _ _ = hTmEqFundTyᵣ'

  syntax homo-step-≡-⟩-∎  x y X Y j x≡y   = x ∷ X heq-≡⟨ x≡y ⟩ j ∣ y ∷ Y ∎
  syntax homo-step-≡-⟨-∎  x y X Y j y≡x   = x ∷ X heq-≡⟨ y≡x ⟨ j ∣ y ∷ Y ∎
  syntax heter-step-≡-⟩-∎ x y X Y x≡y     = x ∷ X heq-≡⟨ x≡y ⟩∣ y ∷ Y ∎
  syntax heter-step-≡-⟨-∎ x y X Y y≡x     = x ∷ X heq-≡⟨ y≡x ⟨∣ y ∷ Y ∎
  syntax conv-step-≡-⟩-A∎  x X Y jX X≡Y     = x ∷ X heq-≡⟨∷ X≡Y ∷⟩∣ jX ⟨∎∷ Y
  syntax conv-step-≡-⟨-A∎  x X Y jX Y≡X     = x ∷ X heq-≡⟨∷ Y≡X ∷⟨∣ jX ⟨∎∷ Y
  syntax conv-step-≡-⟩-B∎  x X Y jY X≡Y     = x ∷ X heq-≡⟨∷ X≡Y ∷⟩∣ jY ⟩∎∷ Y
  syntax conv-step-≡-⟨-B∎  x X Y jY Y≡X     = x ∷ X heq-≡⟨∷ Y≡X ∷⟨∣ jY ⟩∎∷ Y






