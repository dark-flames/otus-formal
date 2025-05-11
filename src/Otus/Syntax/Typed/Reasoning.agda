{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reasoning where

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
  syntax step-≡-∣ x xRy     = x ≡⟨⟩ xRy
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

  syntax step-≡-⟨-∎ x y xRy = x ≡⟨ xRy |⟩ y ∎
  syntax step-≡-⟩-∎ x y yRx = x ≡⟨ yRx ⟨| y ∎

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

  syntax step-≡-⟨-∎ x y A xRy = x ≡⟨ xRy |⟩ y ∎∷ A
  syntax step-≡-⟩-∎ x y A yRx = x ≡⟨ yRx ⟨| y ∎∷ A


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

  syntax step-≡-⟨-∎ x y Δ xRy = x ≡⟨ xRy |⟩ y ∎⇒ Δ
  syntax step-≡-⟩-∎ x y Δ yRx = x ≡⟨ yRx ⟨| y ∎⇒ Δ