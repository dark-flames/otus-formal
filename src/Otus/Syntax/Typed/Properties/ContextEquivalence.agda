{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.ContextEquivalence where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ  : Context
    γ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term
open _⊢_⇒_
open ⊢_
open _⊢_

data ⊢_≃_ : Context → Context → Set where
  PreCEqEmpty : ⊢ ε ≃ ε
  PreCEqExt :  ⊢ Γ ≃ Γ'
      → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B
      → Γ' ⊢ A → Γ' ⊢ B → Γ' ⊢ A ≡ⱼ B
      → ⊢ Γ , A ≃ Γ' , B

preCtxEqExtRefl : ⊢ Γ ≃ Δ → Γ ⊢ A → Δ ⊢ A → ⊢ Γ , A ≃ Δ , A
preCtxEqExtRefl ⊢Γ≃Δ Γ⊢A Δ⊢A = PreCEqExt ⊢Γ≃Δ Γ⊢A Γ⊢A (TyEqRefl Γ⊢A) Δ⊢A Δ⊢A (TyEqRefl Δ⊢A)

preCtxEqRefl : ⊢ Γ → ⊢ Γ ≃ Γ
preCtxEqRefl (CEmp) = PreCEqEmpty
preCtxEqRefl (CExt ⊢Γ Γ⊢A) = let ⊢Γ≡Γ = preCtxEqRefl ⊢Γ
  in preCtxEqExtRefl ⊢Γ≡Γ Γ⊢A Γ⊢A

preCtxEqSym : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Γ
preCtxEqSym eq with eq
... | PreCEqEmpty = PreCEqEmpty
... | PreCEqExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B = 
  PreCEqExt (preCtxEqSym ⊢Γ≃Δ) Δ⊢B Δ⊢A (TyEqSym Δ⊢A≡B) Γ⊢B Γ⊢A (TyEqSym Γ⊢A≡B)

preCtxEqTrans : ⊢ Γ ≃ Δ → ⊢ Δ ≃ Ξ →  ⊢ Γ ≃ Ξ
preCtxEqTrans PreCEqEmpty ⊢ε≃Ξ = ⊢ε≃Ξ
preCtxEqTrans ⊢Γ≃ε PreCEqEmpty = ⊢Γ≃ε
preCtxEqTrans (PreCEqExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (PreCEqExt ⊢Δ≃Ξ _ Δ⊢C Δ⊢B≡C Ξ⊢B Ξ⊢C Ξ⊢B≡C) = 
  let ⊢Γ≃Ξ = preCtxEqTrans ⊢Γ≃Δ ⊢Δ≃Ξ
  in PreCEqExt ⊢Γ≃Ξ Γ⊢A {!   !} {!   !} {!   !} Ξ⊢C {!   !}
            
preCtxEqExtEq : ⊢ Γ → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B → ⊢ Γ , A ≃ Γ , B
preCtxEqExtEq ⊢Γ Γ⊢A Γ⊢B Γ⊢A≡B = PreCEqExt (preCtxEqRefl ⊢Γ) Γ⊢A Γ⊢B Γ⊢A≡B Γ⊢A Γ⊢B Γ⊢A≡B

weakenPreCtxEq : ⊢ Γ ≃ Δ → ⊢ Γ ≡ⱼ Δ
weakenPreCtxEq PreCEqEmpty = CEqRefl CEmp
weakenPreCtxEq (PreCEqExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenPreCtxEq ⊢Γ≃Δ) Γ⊢A Δ⊢B Γ⊢A≡B

weakenPreCtxEq' : ⊢ Γ ≃ Δ → ⊢ Δ ≡ⱼ Γ
weakenPreCtxEq' PreCEqEmpty = CEqRefl CEmp
weakenPreCtxEq' (PreCEqExt ⊢Γ≃Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) = CEqExt (weakenPreCtxEq' ⊢Γ≃Δ) Δ⊢B Γ⊢A (TyEqSym Δ⊢A≡B)

-- ctxEqStability : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
-- conv
