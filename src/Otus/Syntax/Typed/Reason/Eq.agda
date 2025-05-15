{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Eq where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_; _⊔_; lsuc)
open import Otus.Syntax.Typed.Base

private
  variable
    l l₁ l₂ : ULevel
    x y n : ℕ
    Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ δ₃ ξ : Substitution
    A B C D : Term
    f g a b c d : Term

module TyEqReason where
  infix 1 _⊢begin-ty_

  _⊢begin-ty_ : (Γ : Context) →  Γ ⊢ A ≡ⱼ B  → Γ ⊢ A ≡ⱼ B
  Γ ⊢begin-ty aRb = aRb

  infixr 2 ty-step-≡-⟩  ty-step-≡-∣ ty-step-≡-⟨

  ty-step-≡-⟩ : (A : Term) → Γ ⊢ A ≡ⱼ B  → Γ ⊢ B ≡ⱼ C → Γ ⊢ A ≡ⱼ C
  ty-step-≡-⟩ _ = TyEqTrans

  ty-step-≡-∣ : (A : Term) → Γ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
  ty-step-≡-∣ _ aRb = aRb

  ty-step-≡-⟨ : (A : Term) → Γ ⊢ B ≡ⱼ A → Γ ⊢ B ≡ⱼ C → Γ ⊢ A ≡ⱼ C
  ty-step-≡-⟨ _ bRa bRc = TyEqTrans (TyEqSym bRa) bRc

  syntax ty-step-≡-⟩ x xRy yRz  = x ty-≡⟨ xRy ⟩ yRz
  syntax ty-step-≡-∣ x xRy      = x ty-≡⟨⟩ xRy
  syntax ty-step-≡-⟨ x yRx yRz  = x ty-≡⟨ yRx ⟨ yRz
  
  infix 3 ty-step-≡-⟨-∎ ty-step-≡-⟩-∎
  
  ty-step-≡-⟨-∎ : ∀ {Γ} → (A B : Term) → Γ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
  ty-step-≡-⟨-∎ _ _ aRb = aRb

  ty-step-≡-⟩-∎ : ∀ {Γ} → (A B : Term) → Γ ⊢ B ≡ⱼ A → Γ ⊢ A ≡ⱼ B
  ty-step-≡-⟩-∎ _ _ bRa = TyEqSym bRa

  syntax ty-step-≡-⟨-∎ x y xRy = x ty-≡⟨ xRy ⟩∣ y ∎
  syntax ty-step-≡-⟩-∎ x y yRx = x ty-≡⟨ yRx ⟨∣ y ∎


module TmEqReason where
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

module TmHEqReason where
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

module SbEqReason where
  infix 1 _⊢begin-sb_

  _⊢begin-sb_ : (Γ : Context) → Γ ⊢ γ₁ ≡ⱼ  γ₂ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  Γ ⊢begin-sb aRb = aRb

  infixr 2 sb-step-≡-⟩  sb-step-≡-∣ sb-step-≡-⟨

  sb-step-≡-⟩ : (γ₁ : Substitution) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
  sb-step-≡-⟩ _ = SbEqTrans

  sb-step-≡-∣ : (γ₁ : Substitution) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ →  Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-∣ _ aRb = aRb

  sb-step-≡-⟨ : (γ₁ : Substitution) → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
  sb-step-≡-⟨ _ bRa bRc = SbEqTrans (SbEqSym bRa) bRc

  syntax sb-step-≡-⟩ x xRy yRz  = x sb-≡⟨ xRy ⟩ yRz
  syntax sb-step-≡-∣ x xRy      = x sb-≡⟨⟩ xRy
  syntax sb-step-≡-⟨ x yRx yRz  = x sb-≡⟨ yRx ⟨ yRz

  infix 3 sb-step-≡-⟨-∎ sb-step-≡-⟩-∎
  
  sb-step-≡-⟨-∎ : ∀ {Γ} → (γ₁ γ₂ : Substitution) → (Δ : Context) → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-⟨-∎ _ _ _ aRb = aRb

  sb-step-≡-⟩-∎ : ∀ {Γ} → (γ₁ γ₂ : Substitution) → (Δ : Context) → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
  sb-step-≡-⟩-∎ _ _ _ bRa = SbEqSym bRa

  syntax sb-step-≡-⟨-∎ x y Δ xRy = x sb-≡⟨ xRy ⟩∣ y ∎⇒ Δ
  syntax sb-step-≡-⟩-∎ x y Δ yRx = x sb-≡⟨ yRx ⟨∣ y ∎⇒ Δ
