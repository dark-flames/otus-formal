{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Eq where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base


module BeginSyntax
    ( Param :  Set)
    ( Obj : Set )
    ( Relation :  Param → Obj → Obj → Set)
  where

  infix 1 begin_

  begin_ : ∀ {p a b} (d : Relation p a b) → Relation p a b
  begin_ = id

module PBeginSyntax
    ( BParam :  Set )
    ( EParam :  Set )
    ( Obj : Set )
    ( Relation :  (BParam × EParam) → Obj → Obj → Set)
  where

  infix 1 _⊢begin_

  _⊢begin_ : ∀ {ep a b} → (bp : BParam) →  Relation (bp , ep) a b → Relation (bp , ep) a b
  bp ⊢begin aRb = aRb

module ≡Syntax
    ( Param :  Set)
    ( Obj : Set )
    ( Relation :  Param → Obj → Obj → Set)
    ( sym :  ∀ {p : Param} {a b : Obj} → Relation p a b → Relation p b a )
    ( trans : ∀ {p : Param} {a b c : Obj} → Relation p a b → Relation p b c → Relation p a c )
  where

  infixr 2 step-≡-⟩  step-≡-∣ step-≡-⟨

  step-≡-⟩ : ∀ {p b c}  → (a : Obj) → Relation p a b → Relation p b c → Relation p a c
  step-≡-⟩ _ = trans

  step-≡-∣ : ∀ {p b} → (a : Obj) → Relation p a b → Relation p a b
  step-≡-∣ _ aRb = aRb

  step-≡-⟨ : ∀ {p b c} → (a : Obj) → Relation p b a → Relation p b c → Relation p a c
  step-≡-⟨ _ bRa bRc = trans (sym bRa) bRc

  syntax step-≡-⟩ x xRy yRz  = x ≡⟨ xRy ⟩ yRz
  syntax step-≡-∣ x xRy      = x ≡⟨⟩ xRy
  syntax step-≡-⟨ x yRx yRz  = x ≡⟨ yRx ⟨ yRz


module EndSyntax
  ( Param :  Set)
  ( Obj : Set )
  ( Relation :  Param → Obj → Obj → Set)
  ( sym :  ∀ {p : Param} {a b : Obj} → Relation p a b → Relation p b a )
  where
  
  infix 3 step-≡-⟨-∎ step-≡-⟩-∎
  
  step-≡-⟨-∎ : ∀ {p} → (a : Obj) → (b : Obj) → Relation p a b → Relation p a b
  step-≡-⟨-∎ _ _ aRb = aRb

  step-≡-⟩-∎ : ∀ {p} → (a : Obj) → (b : Obj) → Relation p b a → Relation p a b
  step-≡-⟩-∎ _ _ bRa = sym bRa

  syntax step-≡-⟨-∎ x y xRy = x ≡⟨ xRy ⟩∣ y ∎
  syntax step-≡-⟩-∎ x y yRx = x ≡⟨ yRx ⟨∣ y ∎

module ContextEqReasoning where
  open import Otus.Syntax.Typed.Properties.Context
  ContextEq : ⊤ → Context → Context → Set
  ContextEq _ = ⊢_≡ⱼ_

  sym : ∀ {p : ⊤} {Γ Δ} → ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Γ
  sym {p} = ctxEqSym

  trans : ∀ {p : ⊤} {Γ Δ Ξ} → ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ 
  trans {p} = ctxEqTrans

  open BeginSyntax ⊤ Context ContextEq public
  open ≡Syntax ⊤ Context ContextEq sym trans public
  open EndSyntax ⊤ Context ContextEq sym public
  

module TyEqReasoning where
  TyEq : (Context × ⊤) → Term → Term → Set
  TyEq (Γ , _) A B = Γ ⊢ A ≡ⱼ B

  open PBeginSyntax Context ⊤ Term TyEq public
  open ≡Syntax (Context × ⊤) Term TyEq TyEqSym TyEqTrans public
  open EndSyntax (Context × ⊤) Term TyEq TyEqSym public

module TmEqReasoning where
  TmEq : (Context × Term) → Term → Term → Set
  TmEq (Γ , A) a b = Γ ⊢ a ≡ⱼ b ∷ A

  sym : ∀ {p : (Context × Term)} {a b} 
    → (proj₁ p) ⊢ a ≡ⱼ b ∷ (proj₂ p) 
    → (proj₁ p) ⊢ b ≡ⱼ a ∷ (proj₂ p)
  sym Γ⊢a≡b∷A = TmEqSym Γ⊢a≡b∷A

  trans : ∀ {p : (Context × Term)} {a b c} 
    → (proj₁ p) ⊢ a ≡ⱼ b ∷ (proj₂ p) → (proj₁ p) ⊢ b ≡ⱼ c ∷ (proj₂ p) 
    → (proj₁ p) ⊢ a ≡ⱼ c ∷ (proj₂ p)
  trans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A

  open PBeginSyntax Context Term Term TmEq public
  open ≡Syntax (Context × Term) Term TmEq sym trans public
  
  infix 3 step-≡-⟨-∎ step-≡-⟩-∎
  
  step-≡-⟨-∎ : ∀ {Γ} → (a b : Term) → (A : Term) → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  step-≡-⟨-∎ _ _ _ aRb = aRb

  step-≡-⟩-∎ : ∀ {Γ} → (a b : Term) → (A : Term) → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
  step-≡-⟩-∎ _ _ _ bRa = TmEqSym bRa

  syntax step-≡-⟨-∎ x y A xRy = x ≡⟨ xRy ⟩∣ y ∎∷ A
  syntax step-≡-⟩-∎ x y A yRx = x ≡⟨ yRx ⟨∣ y ∎∷ A

module TmHEqReasoning where
  open import Otus.Syntax.Typed.Properties.Heterogeneous

  TmHEq : (Context × (Term × Term)) → Term → Term → Set
  TmHEq (Γ , (A , B)) a b = Γ ⊢ a ∷ A ≡ⱼ b ∷ B

  open PBeginSyntax Context (Term × Term) Term TmHEq public

  private
    variable 
      Γ : Context
      A B C a b c : Term

  infix 1 _⊢beginₗ_ _⊢beginᵣ_

  _⊢beginₗ_ : (Γ : Context) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ A
  Γ ⊢beginₗ Γ⊢a∷A≡b∷B = hEqWeakenₗ Γ⊢a∷A≡b∷B

  _⊢beginᵣ_ : (Γ : Context) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ≡ⱼ b ∷ B
  Γ ⊢beginᵣ Γ⊢a∷A≡b∷B = hEqWeakenᵣ Γ⊢a∷A≡b∷B

  infixr 2 homoStep-≡-⟩ homoStep-≡-⟨ step-≡-∣ heterStepₗ-≡-⟩ heterStepₗ-≡-⟨ heterStepᵣ-≡-⟩ heterStepᵣ-≡-⟨

  homoStep-≡-⟩ : (a B : Term) → Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  homoStep-≡-⟩ _ _ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C = hEqHomoTransₗ Γ⊢a≡b∷B Γ⊢b∷B≡c∷C
  homoStep-≡-⟨ : (a B : Term) → Γ ⊢ b ≡ⱼ a ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  homoStep-≡-⟨ _ _ Γ⊢b≡a∷B Γ⊢b∷B≡c∷C = hEqHomoTransₗ (TmEqSym Γ⊢b≡a∷B) Γ⊢b∷B≡c∷C

  step-≡-∣ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
  step-≡-∣ _ _ Γ⊢a∷A≡b∷B = Γ⊢a∷A≡b∷B
  -- by heter
  heterStepₗ-≡-⟩ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
  heterStepₗ-≡-⟩ _ _ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = hEqTrans Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C

  heterStepₗ-≡-⟨ : (a A : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ A ≡ⱼ c ∷ C
  heterStepₗ-≡-⟨ _ _ Γ⊢b∷B≡a∷A Γ⊢b∷B≡c∷C = hEqTrans (hEqSym Γ⊢b∷B≡a∷A) Γ⊢b∷B≡c∷C

  heterStepᵣ-≡-⟩ : (a A : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  heterStepᵣ-≡-⟩ _ _ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C = hEqTransᵣ Γ⊢a∷A≡b∷B Γ⊢b∷B≡c∷C

  heterStepᵣ-≡-⟨ : (a A : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ b ∷ B ≡ⱼ c ∷ C → Γ ⊢ a ∷ B ≡ⱼ c ∷ C
  heterStepᵣ-≡-⟨ _ _ Γ⊢b∷B≡a∷A Γ⊢b∷B≡c∷C = hEqTransᵣ (hEqSym Γ⊢b∷B≡a∷A) Γ⊢b∷B≡c∷C

  syntax homoStep-≡-⟩ x X x≡y y≡z     = x ∷ X ≡⟨ x≡y ⟩ y≡z
  syntax homoStep-≡-⟨ x y≡x y≡z       = x ∷ X ≡⟨ y≡x ⟨ y≡z
  syntax step-≡-∣ x X x≡y             = x ∷ X ≡⟨⟩ x≡y
  syntax heterStepₗ-≡-⟩ x X x≡y y≡z    = x ∷ X ≡⟨∣ x≡y ∙⟩ y≡z
  syntax heterStepₗ-≡-⟨ x X y≡x y≡z    = x ∷ X ≡⟨∣ y≡x ∙⟨ y≡z
  syntax heterStepᵣ-≡-⟩ x X x≡y y≡z   = x ∷ X ≡⟨∙ x≡y ∣⟩ y≡z
  syntax heterStepᵣ-≡-⟨ x X y≡x y≡z   = x ∷ X ≡⟨∙ y≡x ∣⟨ y≡z


  infixr 3 heterStep-≡-⟩-∎ heterStep-≡-⟨-∎ homoStep-≡-⟩-∎ homoStep-≡-⟩-∎

  homoStep-≡-⟩-∎ : (a b A B : Term) → Γ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
  homoStep-≡-⟩-∎ _ _ _ _ = hEqFund
  
  homoStep-≡-⟨-∎ : (a b A B : Term) → Γ ⊢ A → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
  homoStep-≡-⟨-∎ _ _ _ _ = hEqFund' 

  homoStep-≡-|-∎ : (a b A B : Term) → Γ ⊢ A → Γ ⊢ b ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ A
  homoStep-≡-|-∎ _ _ _ _ = hEqFund' 

  heterStep-≡-⟩-∎ : (a b A B : Term) → Γ ⊢ a ∷ A ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B 
  heterStep-≡-⟩-∎ _ _ _ _ Γ⊢a∷A≡b∷B = Γ⊢a∷A≡b∷B

  heterStep-≡-⟨-∎ : (a b A B : Term) → Γ ⊢ b ∷ B ≡ⱼ a ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ B 
  heterStep-≡-⟨-∎ _ _ _ _ Γ⊢b∷B≡a∷A = hEqSym Γ⊢b∷B≡a∷A

  syntax homoStep-≡-⟩-∎  x y X Y j x≡y   = x ∷ X ≡⟨ x≡y ⟩ j ∣ y ∷ Y ∎
  syntax homoStep-≡-⟨-∎  x y X Y j y≡x   = x ∷ X ≡⟨ y≡x ⟨ j ∣ y ∷ Y ∎
  syntax heterStep-≡-⟩-∎ x y X Y x≡y = x ∷ X ≡⟨ x≡y ⟩∣ y ∷ Y ∎
  syntax heterStep-≡-⟨-∎ x y X Y y≡x = x ∷ X ≡⟨ y≡x ⟨∣ y ∷ Y ∎

module SbEqReasoning where
  SbEq : (Context × Context) → Substitution → Substitution → Set
  SbEq (Γ , Δ) γ δ = Γ ⊢ γ ≡ⱼ δ ⇒ Δ

  sym : ∀ {p : (Context × Context)} {γ δ} 
    → (proj₁ p) ⊢ γ ≡ⱼ δ ⇒ (proj₂ p) 
    → (proj₁ p) ⊢ δ ≡ⱼ γ ⇒ (proj₂ p)
  sym Γ⊢γ≡δ⇒Δ = SbEqSym Γ⊢γ≡δ⇒Δ

  trans : ∀ {p : (Context × Context)} {γ δ ξ} 
    → (proj₁ p) ⊢ γ ≡ⱼ δ ⇒ (proj₂ p) → (proj₁ p) ⊢ δ ≡ⱼ ξ ⇒ (proj₂ p) 
    → (proj₁ p) ⊢ γ ≡ⱼ ξ ⇒ (proj₂ p)
  trans Γ⊢γ≡δ⇒Δ Γ⊢δ≡ξ⇒Δ = SbEqTrans Γ⊢γ≡δ⇒Δ Γ⊢δ≡ξ⇒Δ

  open PBeginSyntax Context Context Substitution SbEq public
  open ≡Syntax (Context × Context) Substitution SbEq sym trans public
  -- open EndSyntax (Context × Context) Substitution SbEq sym public
  infix 3 step-≡-⟨-∎ step-≡-⟩-∎
  
  step-≡-⟨-∎ : ∀ {Γ} → (a b : Substitution) → (Δ : Context) → Γ ⊢ a ≡ⱼ b ⇒ Δ → Γ ⊢ a ≡ⱼ b ⇒ Δ
  step-≡-⟨-∎ _ _ _ aRb = aRb

  step-≡-⟩-∎ : ∀ {Γ} → (a b : Substitution) → (Δ : Context) → Γ ⊢ b ≡ⱼ a ⇒ Δ → Γ ⊢ a ≡ⱼ b ⇒ Δ
  step-≡-⟩-∎ _ _ _ bRa = SbEqSym bRa

  syntax step-≡-⟨-∎ x y Δ xRy = x ≡⟨ xRy ⟩∣ y ∎⇒ Δ
  syntax step-≡-⟩-∎ x y Δ yRx = x ≡⟨ yRx ⟨∣ y ∎⇒ Δ