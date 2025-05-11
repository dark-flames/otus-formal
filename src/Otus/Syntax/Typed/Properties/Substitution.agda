{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Substitution where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Reasoning
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion


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
      Γ ▷ A ⊢begin
        drop x ∘ drop (1 + y)
      ≡⟨ substEqComp₂ Δ⊢dropX⇒Ξ (SbEqDropComp Γ⊢dropY⇒Δ Γ▷A⊢drop1⇒Γ) ⟨
        drop x ∘ (drop y ∘ drop 1)
      ≡⟨ SbEqCompAssoc Δ⊢dropX⇒Ξ Γ⊢dropY⇒Δ Γ▷A⊢drop1⇒Γ ⟨
        drop x ∘ drop y ∘ drop 1
      ≡⟨ substEqComp₁ Γ⊢dropX∘dropY≡dropY+X⇒Ξ Γ▷A⊢drop1⇒Γ ⟩
        drop (y + x) ∘ drop 1
      ≡⟨ SbEqDropComp Γ⊢dropY+X⇒Ξ Γ▷A⊢drop1⇒Γ ⟩
        drop (1 + (y + x))
      ≡⟨ substEqDrop Γ▷A⊢drop1+Y+X⇒Ξ refl ⟨|
        drop (1 + y + x)
      ∎⇒ Ξ
  in Γ▷A⊢drop1+Y+X⇒Ξ , Γ▷A⊢dropX∘drop1+Y≡drop1+Y+X⇒Ξ
dropCompEq {_} { x } {Ξ} {_} { suc y } Δ₂⊢dropX⇒Ξ (SbConv Γ⊢dropSY⇒Δ₁ ⊢Δ₁≡Δ₂) = let
    Δ₁⊢dropX⇒Ξ = substStability' ⊢Δ₁≡Δ₂ Δ₂⊢dropX⇒Ξ
  in dropCompEq Δ₁⊢dropX⇒Ξ Γ⊢dropSY⇒Δ₁

{-
liftVar : Δ ⊢ A → Δ ⊢ Var x ∷ A → Γ ⊢ drop y ⇒ Δ
  → Γ ⊢ Var x [ drop y ]ₑ ≡ⱼ Var (y + x) ∷ A [ drop y ]ₑ
liftVar {Δ} {A} {x} {Γ} {zero} Δ⊢A Δ⊢VarX∷A Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
    Γ⊢VarX∷A = tmStability' ⊢Γ≡Δ Δ⊢VarX∷A
    Γ⊢A = tyStability' ⊢Γ≡Δ Δ⊢A
    Γ⊢A≡A[id] = TyEqSubstId Γ⊢A
  in TmEqConv (TmEqSubstId Γ⊢VarX∷A) (TyEqSym Γ⊢A≡A[id])
liftVar {Δ} {A} {x} {Γ} {suc y} Δ⊢A Δ⊢VarX∷A Γ⊢dropSY⇒Δ = let 
    dropSucInv Γ' B Γ'⊢B ⊢Γ≡Γ'▷B Γ'⊢dropY⇒Δ = dropSucInversion Γ⊢dropSY⇒Δ
    Γ⊢drop1⇒Γ' = substStability' ⊢Γ≡Γ'▷B (displayMap Γ'⊢B)
    Γ'⊢VarX[dropY]≡VarY+X∷A[dropY] = liftVar Δ⊢A Δ⊢VarX∷A Γ'⊢dropY⇒Δ
    Γ⊢VarX[dropY][drop1]≡VarY[drop1]+X∷A[dropY][drop1] = 
      TmEqSubst {!   !} Γ'⊢VarX[dropY]≡VarY+X∷A[dropY] (SbEqRefl Γ⊢drop1⇒Γ')
  in {!   !}-}