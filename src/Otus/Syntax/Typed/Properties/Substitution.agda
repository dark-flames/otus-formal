{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Substitution where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Reason
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion
open import Otus.Syntax.Typed.Properties.Heterogeneous


private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term
{-
Substitution lemmas related to context conversion and inversion lemma
-}

dropCompEq : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop y ⇒ Δ
  → Γ ⊢ drop (y + x) ⇒ Ξ × Γ ⊢ drop x ∘ drop y ≡ⱼ drop (y + x) ⇒ Ξ
dropCompEq {_} { x } {_} {_} { zero } Δ⊢dropX⇒Ξ Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in substStability' ⊢Γ≡Δ Δ⊢dropX⇒Ξ , SbEqIdᵣ Δ⊢dropX⇒Ξ Γ⊢id⇒Δ
dropCompEq {_} { x } {Ξ} {_} { suc y } Δ⊢dropX⇒Ξ (SbDropˢ {Γ} {_} {_} {A} Γ⊢dropY⇒Δ Γ⊢A) = let
    Γ⊢dropY+X⇒Ξ , Γ⊢dropX∘dropY≡dropY+X⇒Ξ = dropCompEq Δ⊢dropX⇒Ξ Γ⊢dropY⇒Δ
    Γ▷A⊢drop1⇒Γ = displayMap Γ⊢A
    Γ▷A⊢drop1+Y+X⇒Ξ = SbDropˢ Γ⊢dropY+X⇒Ξ Γ⊢A
    open SbEqReasoning
    Γ▷A⊢dropX∘drop1+Y≡drop1+Y+X⇒Ξ = 
      Γ ▷ A ⊢begin-sb
        drop x ∘ drop (1 + y)
      sb-≡⟨ substEqComp₂ Δ⊢dropX⇒Ξ (SbEqDropComp Γ⊢dropY⇒Δ Γ▷A⊢drop1⇒Γ) ⟨
        drop x ∘ (drop y ∘ drop 1)
      sb-≡⟨ SbEqCompAssoc Δ⊢dropX⇒Ξ Γ⊢dropY⇒Δ Γ▷A⊢drop1⇒Γ ⟨
        drop x ∘ drop y ∘ drop 1
      sb-≡⟨ substEqComp₁ Γ⊢dropX∘dropY≡dropY+X⇒Ξ Γ▷A⊢drop1⇒Γ ⟩
        drop (y + x) ∘ drop 1
      sb-≡⟨ SbEqDropComp Γ⊢dropY+X⇒Ξ Γ▷A⊢drop1⇒Γ ⟩
        drop (1 + (y + x))
      sb-≡⟨ substEqDrop Γ▷A⊢drop1+Y+X⇒Ξ refl ⟨∣
        drop (1 + y + x)
      ∎⇒ Ξ
  in Γ▷A⊢drop1+Y+X⇒Ξ , Γ▷A⊢dropX∘drop1+Y≡drop1+Y+X⇒Ξ
dropCompEq {_} { x } {Ξ} {_} { suc y } Δ₂⊢dropX⇒Ξ (SbConv Γ⊢dropSY⇒Δ₁ ⊢Δ₁≡Δ₂) = let
    Δ₁⊢dropX⇒Ξ = substStability' ⊢Δ₁≡Δ₂ Δ₂⊢dropX⇒Ξ
  in dropCompEq Δ₁⊢dropX⇒Ξ Γ⊢dropSY⇒Δ₁


liftVar : Δ ⊢ A → Δ ⊢ Var x ∷ A → Γ ⊢ drop y ⇒ Δ
  → Γ ⊢ Var (y + x) ∷ A [ drop y ]ₑ
liftVar {Δ} {A} {x} {Γ} {zero} Δ⊢A Δ⊢VarX∷A Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
    Γ⊢VarX∷A = tmStability' ⊢Γ≡Δ Δ⊢VarX∷A
    Γ⊢A = tyStability' ⊢Γ≡Δ Δ⊢A
    Γ⊢A[id]≡A = TyEqSubstId Γ⊢A
  in tmTyConv' Γ⊢VarX∷A Γ⊢A[id]≡A
liftVar {Δ} {A} {x} {Γ} {suc y} Δ⊢A Δ⊢VarX∷A Γ⊢dropSY⇒Δ = let
    dropSucInv Γ' B Γ'⊢B ⊢Γ≡Γ'▷B Γ'⊢dropY⇒Δ = dropSucInversion Γ⊢dropSY⇒Δ
    Γ⊢drop1⇒Γ' = substStability' ⊢Γ≡Γ'▷B (displayMap Γ'⊢B)
    in begin
      by-⟨ liftVar Δ⊢A Δ⊢VarX∷A Γ'⊢dropY⇒Δ ⟩
      Γ' ⊢ Var (y + x) ∷ A [ drop y ]ₑ 
    ⎯⎯⎯⎯⟨ Tm-Var-ext Γ'⊢B ⟩
      Γ' ▷ B ⊢ Var (1 + (y + x)) ∷ A [ drop y ]ₑ [ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-Stability' ⊢Γ≡Γ'▷B ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop y ]ₑ [ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Γ'⊢dropY⇒Δ Γ⊢drop1⇒Γ' Δ⊢A) ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop y ∘ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ⊢A (SbEqDropComp Γ'⊢dropY⇒Δ Γ⊢drop1⇒Γ')) ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop (1 + y) ]ₑ
    ∎