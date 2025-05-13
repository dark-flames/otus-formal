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

substWfCodomain : Γ ⊢ γ ⇒ Δ → ⊢ Δ
substWfCodomain sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⊢dropX⇒Δ _ = substWfCodomain Γ⊢dropX⇒Δ
...| SbExt Γ⊢γ⇒Δ Δ⊢A _ = CExt (substWfCodomain Γ⊢γ⇒Δ) Δ⊢A
...| SbComp Δ⊢δ⇒Ξ _ = substWfCodomain Δ⊢δ⇒Ξ
...| SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)

substEqWfCodomain : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Δ
substEqWfCodomain eq with eq
...| SbEqRefl Γ⊢γ⇒Δ = substWfCodomain Γ⊢γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = substEqWfCodomain Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = substEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A _ = CExt (substEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ) Δ⊢A
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ _ = substEqWfCodomain Δ⊢δ₁≡δ₂⇒Ξ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)
...| SbEqCompAssoc Ξ⊢ξ⇒Θ _ _ = substWfCodomain Ξ⊢ξ⇒Θ
...| SbEqIdₗ Δ⊢id⇒Ξ _ = substWfCodomain Δ⊢id⇒Ξ
...| SbEqIdᵣ Δ⊢γ⇒Ξ _ = substWfCodomain Δ⊢γ⇒Ξ
...| SbEqExtVar Γ⊢Var0∷A = tmWfCtx Γ⊢Var0∷A
...| SbEqDropExt Δ⊢drop1⇒Ξ _ = substWfCodomain Δ⊢drop1⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ _ = substWfCodomain Δ⊢dropX⇒Ξ
...| SbEqExtComp Δ⊢δ▶a⇒Ξ _ = substWfCodomain Δ⊢δ▶a⇒Ξ

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


substDrop1CompComm : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop 1 ⇒ Δ
    → Σ[ Δ' ∈ Context ] 
    (Γ ⊢ drop x ⇒ Δ') ×
    (Δ' ⊢ drop 1 ⇒ Ξ) ×
    Γ ⊢ drop x ∘ drop 1 ≡ⱼ drop 1 ∘ drop x ⇒ Ξ
substDrop1CompComm {_} { zero } {Ξ} {Γ} Δ⊢id⇒Ξ Γ⊢drop1⇒Δ = let
    ⊢Δ≡Ξ = idInversion Δ⊢id⇒Ξ
    ⊢Γ = substWfCtx Γ⊢drop1⇒Δ
    Γ⊢id⇒Γ = SbId ⊢Γ
    Γ⊢drop1⇒Ξ = (SbConv Γ⊢drop1⇒Δ ⊢Δ≡Ξ)
    open SbEqReasoning
  in Γ , Γ⊢id⇒Γ , Γ⊢drop1⇒Ξ , (
    Γ ⊢begin-sb
      idₛ ∘ drop 1 
    sb-≡⟨ SbEqIdₗ Δ⊢id⇒Ξ Γ⊢drop1⇒Δ ⟩
      drop 1
    sb-≡⟨ SbEqIdᵣ Γ⊢drop1⇒Ξ Γ⊢id⇒Γ ⟨∣
      drop 1 ∘ idₛ
    ∎⇒ Ξ
  )
substDrop1CompComm {Δ} { suc x } {Ξ} {Γ} Δ⊢drop-sx⇒Ξ Γ⊢drop1⇒Δ = let
    dropSucInv Δ₁ A Δ₁⊢A ⊢Δ≡Δ₁▷A Δ₁⊢drop-x⇒Ξ = dropSucInversion Δ⊢drop-sx⇒Ξ
    ctxExtInv Γ' A Γ'⊢A ⊢Γ≡Γ'▷A , ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
    Δ₁▷A⊢drop1⇒Δ₁ = displayMap Δ₁⊢A
    Δ⊢drop1⇒Δ₁ = substStability' ⊢Δ≡Δ₁▷A Δ₁▷A⊢drop1⇒Δ₁
    Δ₂ , Δ⊢drop-x⇒Δ₂ , Δ₂⊢drop1⇒Ξ , Δ⊢drop-x∘drop-1≡drop-1∘dropx⇒Ξ = substDrop1CompComm Δ₁⊢drop-x⇒Ξ Δ⊢drop1⇒Δ₁
    open SbEqReasoning
    Γ⊢drop-sx⇒Δ₂ = begin
        intro-⟨ Δ⊢drop-x⇒Δ₂ ⟩
        Δ ⊢ drop x ⇒ Δ₂
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ'≡Δ ⟩
        Γ' ⊢ drop x ⇒ Δ₂
      ⎯⎯⎯⎯⟨ Sb-Dropₛ-ext Γ'⊢A ⟩
        Γ' ▷ A ⊢ drop (1 + x) ⇒ Δ₂
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ≡Γ'▷A ⟩
        Γ ⊢ drop (1 + x) ⇒ Δ₂
      ∎
  in Δ₂ , Γ⊢drop-sx⇒Δ₂ , Δ₂⊢drop1⇒Ξ , (
    Γ ⊢begin-sb
      drop (1 + x) ∘ drop 1
    sb-≡⟨ substEqComp₁ (SbEqDropComp Δ₁⊢drop-x⇒Ξ Δ⊢drop1⇒Δ₁) Γ⊢drop1⇒Δ ⟨
      drop x ∘ drop 1 ∘ drop 1 
    sb-≡⟨ substEqComp₁ Δ⊢drop-x∘drop-1≡drop-1∘dropx⇒Ξ Γ⊢drop1⇒Δ ⟩
      drop 1 ∘ drop x ∘ drop 1 
    sb-≡⟨ SbEqCompAssoc Δ₂⊢drop1⇒Ξ Δ⊢drop-x⇒Δ₂ Γ⊢drop1⇒Δ ⟩
      drop 1 ∘ (drop x ∘ drop 1)
    sb-≡⟨ substEqComp₂ Δ₂⊢drop1⇒Ξ (SbEqDropComp Δ⊢drop-x⇒Δ₂ Γ⊢drop1⇒Δ) ⟩∣
      drop 1 ∘ drop (1 + x) 
    ∎⇒ Ξ
  )

substDropCompComm : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop y ⇒ Δ
  → Σ[ Δ' ∈ Context ] 
    (Γ ⊢ drop x ⇒ Δ') ×
    (Δ' ⊢ drop y ⇒ Ξ) ×
    Γ ⊢ drop y ∘ drop x ≡ⱼ drop x ∘ drop y ⇒ Ξ
substDropCompComm {_} { x } {Ξ} {Γ} { zero } Δ⊢drop-x⇒Ξ Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
    Ξ⊢id⇒Ξ = SbId (substWfCodomain Δ⊢drop-x⇒Ξ)
    Γ⊢drop-x⇒Ξ = substStability' ⊢Γ≡Δ Δ⊢drop-x⇒Ξ
    open SbEqReasoning
  in Ξ , Γ⊢drop-x⇒Ξ , Ξ⊢id⇒Ξ , (
    Γ ⊢begin-sb
      idₛ ∘ drop x  
    sb-≡⟨ SbEqIdₗ Ξ⊢id⇒Ξ Γ⊢drop-x⇒Ξ ⟩
      drop x
    sb-≡⟨ SbEqIdᵣ Δ⊢drop-x⇒Ξ Γ⊢id⇒Δ ⟨∣
      drop x ∘ idₛ
    ∎⇒ Ξ
  )
substDropCompComm {_} { x } {Ξ} {Γ} { suc y } Δ⊢drop-x⇒Ξ Γ⊢drop-sy⇒Δ = let
    dropSucInv Γ₁ A Γ₁⊢A ⊢Γ≡Γ₁▷A Γ₁⊢drop-y⇒Δ = dropSucInversion Γ⊢drop-sy⇒Δ
    Δ₁ , Γ₁⊢drop-x⇒Δ₁ , Δ₁⊢drop-y⇒Ξ , Γ₁⊢drop-y∘drop-x≡drop-x∘drop-y⇒Ξ 
      = substDropCompComm Δ⊢drop-x⇒Ξ Γ₁⊢drop-y⇒Δ
    Γ⊢drop1⇒Γ₁ = substStability' ⊢Γ≡Γ₁▷A (displayMap Γ₁⊢A)
    Γ₂ , Γ⊢drop-x⇒Γ₂ , Γ₂⊢drop1⇒Δ₁ , Γ⊢drop-x∘drop1≡drop1∘dropx⇒Δ₁ 
      = substDrop1CompComm Γ₁⊢drop-x⇒Δ₁ Γ⊢drop1⇒Γ₁
    ctxExtInv Γ₃ B Γ₃⊢B ⊢Γ₂≡Γ₃▷B , ⊢Γ₃≡Δ₁ = drop1Inversion Γ₂⊢drop1⇒Δ₁
    Γ₂⊢drop-sy⇒Ξ = 
      begin
        intro-⟨ Δ₁⊢drop-y⇒Ξ ⟩
        Δ₁  ⊢ drop y ⇒ Ξ
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ₃≡Δ₁ ⟩
        Γ₃  ⊢ drop y ⇒ Ξ
      ⎯⎯⎯⎯⟨ Sb-Dropₛ-ext Γ₃⊢B ⟩
        Γ₃ ▷ B ⊢ drop (1 + y) ⇒ Ξ
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ₂≡Γ₃▷B ⟩
        Γ₂ ⊢ drop (1 + y) ⇒ Ξ
      ∎
    open SbEqReasoning
  in Γ₂ , Γ⊢drop-x⇒Γ₂ , Γ₂⊢drop-sy⇒Ξ , (
    Γ ⊢begin-sb
      drop (1 + y) ∘ drop x
    sb-≡⟨ substEqComp₁ (SbEqDropComp Δ₁⊢drop-y⇒Ξ Γ₂⊢drop1⇒Δ₁) Γ⊢drop-x⇒Γ₂ ⟨
      drop y ∘ drop 1 ∘ drop x
    sb-≡⟨ SbEqCompAssoc Δ₁⊢drop-y⇒Ξ Γ₂⊢drop1⇒Δ₁ Γ⊢drop-x⇒Γ₂ ⟩
      drop y ∘ (drop 1 ∘ drop x)
    sb-≡⟨ substEqComp₂ Δ₁⊢drop-y⇒Ξ Γ⊢drop-x∘drop1≡drop1∘dropx⇒Δ₁ ⟨
      drop y ∘ (drop x ∘ drop 1)
    sb-≡⟨ SbEqCompAssoc Δ₁⊢drop-y⇒Ξ Γ₁⊢drop-x⇒Δ₁ Γ⊢drop1⇒Γ₁ ⟨
      drop y ∘ drop x ∘ drop 1
    sb-≡⟨ substEqComp₁ Γ₁⊢drop-y∘drop-x≡drop-x∘drop-y⇒Ξ Γ⊢drop1⇒Γ₁ ⟩
      drop x ∘ drop y ∘ drop 1
    sb-≡⟨ SbEqCompAssoc Δ⊢drop-x⇒Ξ Γ₁⊢drop-y⇒Δ Γ⊢drop1⇒Γ₁ ⟩
      drop x ∘ (drop y ∘ drop 1)
    sb-≡⟨ substEqComp₂ Δ⊢drop-x⇒Ξ (SbEqDropComp Γ₁⊢drop-y⇒Δ Γ⊢drop1⇒Γ₁) ⟩∣
      drop x ∘ drop (1 + y)
    ∎⇒ Ξ
  )

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
      intro-⟨ liftVar Δ⊢A Δ⊢VarX∷A Γ'⊢dropY⇒Δ ⟩
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

{-}
substEqDropSExtVar : Γ ⊢ drop x ⇒ Δ → Γ ⊢ Var 0 ∷ A
  →  Γ ⊢ drop (1 + x) ▶ Var 0 ≡ⱼ drop x  ⇒ Δ
substEqDropSExtVar {Γ} {zero} {Δ} {A} Γ⊢id⇒Δ Γ⊢Var0∷A = let
     ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in SbEqConv (SbEqExtVar Γ⊢Var0∷A) ⊢Γ≡Δ
substEqDropSExtVar {Γ} {suc x} {Δ} {A} Γ⊢drop-sx⇒Δ Γ⊢Var0∷A = let
    dropSucInv Γ₁ A Γ₁⊢A ⊢Γ≡Γ₁▷A Γ₁⊢drop-x⇒Δ = dropSucInversion Γ⊢drop-sx⇒Δ
    Γ₁▷A⊢drop1⇒Γ₁ = displayMap Γ₁⊢A
    Γ⊢drop1⇒Γ₁ = substStability' ⊢Γ≡Γ₁▷A Γ₁▷A⊢drop1⇒Γ₁
    Δ₁ , Γ⊢drop-x⇒Δ₁ , Δ₁⊢drop1⇒Δ , Γ⊢drop-x∘drop1≡drop1∘dropx⇒Δ 
      = substDrop1CompComm Γ₁⊢drop-x⇒Δ Γ⊢drop1⇒Γ₁
    Γ⊢drop-sx▶Var0≡drop-x⇒Δ = substEqDropSExtVar Γ⊢drop-x⇒Δ₁ Γ⊢VarX∷A
    open SbEqReasoning
    test =
      ⊢begin-sb
        drop (1 + (1 + x)) ▶ Var 1
      sb-≡⟨ {!   !} ⟩
        (drop (x + 1) ∘ drop 1) ▶ Var 0[drop 1]
      sb-≡⟨ {!   !} ⟩
        (drop (1 + x) ▶ Var 0) ∘ drop 1
      sb-≡⟨ {!   !} ⟩
        drop x ∘ drop 1
      sb-≡⟨ {!   !} ⟩∣
        drop (1 + x)
      ∎⇒ Δ
    -- drop (1 + x) ▶ Var x ≡ⱼ drop x
  in ?-}
      
  
  