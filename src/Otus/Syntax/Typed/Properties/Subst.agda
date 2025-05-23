{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Subst where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Reason
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Inversion
open import Otus.Syntax.Typed.Properties.Heter


private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ  : Context
    γ γ₁ γ₂ : Substitution
    A B a b : Term

{-
Substitution lemmas related to context conversion and inversion lemma
-}

sbWfCodomain : Γ ⊢ γ ⇒ Δ → ⊢ Δ
sbWfCodomain sb with sb
...| SbId ⊢Γ = ⊢Γ
...| SbDropˢ Γ⊢dropX⇒Δ _ = sbWfCodomain Γ⊢dropX⇒Δ
...| SbExt Γ⊢γ⇒Δ Δ⊢A _ = CExt (sbWfCodomain Γ⊢γ⇒Δ) Δ⊢A
...| SbComp Δ⊢δ⇒Ξ _ = sbWfCodomain Δ⊢δ⇒Ξ
...| SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)

sbEqWfCodomain : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → ⊢ Δ
sbEqWfCodomain eq with eq
...| SbEqRefl Γ⊢γ⇒Δ = sbWfCodomain Γ⊢γ⇒Δ
...| SbEqSym Γ⊢γ₂≡γ₁⇒Δ = sbEqWfCodomain Γ⊢γ₂≡γ₁⇒Δ
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Δ _ = sbEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ
...| SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A _ = CExt (sbEqWfCodomain Γ⊢γ₁≡γ₂⇒Δ) Δ⊢A
...| SbEqComp Δ⊢δ₁≡δ₂⇒Ξ _ = sbEqWfCodomain Δ⊢δ₁≡δ₂⇒Ξ
...| SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = proj₂ (ctxEqWfCtx ⊢Δ₁≡Δ₂)
...| SbEqCompAssoc Ξ⊢ξ⇒Θ _ _ = sbWfCodomain Ξ⊢ξ⇒Θ
...| SbEqIdₗ Δ⊢id⇒Ξ _ = sbWfCodomain Δ⊢id⇒Ξ
...| SbEqIdᵣ Δ⊢γ⇒Ξ _ = sbWfCodomain Δ⊢γ⇒Ξ
...| SbEqExtVar Γ⊢Var0∷A = tmWfCtx Γ⊢Var0∷A
...| SbEqDropExt Δ⊢drop1⇒Ξ _ = sbWfCodomain Δ⊢drop1⇒Ξ
...| SbEqDropComp Δ⊢dropX⇒Ξ _ = sbWfCodomain Δ⊢dropX⇒Ξ
...| SbEqExtComp Δ⊢δ◀a⇒Ξ _ = sbWfCodomain Δ⊢δ◀a⇒Ξ

sbExtNat : Γ ⊢ γ ⇒ Δ → Γ ⊢ a ∷ Nat
    → Γ ⊢ γ ◀ a ⇒ Δ ◁ Nat
sbExtNat Γ⊢γ⇒Δ Γ⊢a∷ℕ = let
    ⊢Δ = sbWfCodomain Γ⊢γ⇒Δ
    Γ⊢a∷Nat[γ] = TmTyConv Γ⊢a∷ℕ (TyEqSym (TyEqNatSubst Γ⊢γ⇒Δ))
  in SbExt Γ⊢γ⇒Δ (TyNat ⊢Δ) Γ⊢a∷Nat[γ]

dropCompEq : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop y ⇒ Δ
  → (Γ ⊢ drop (y + x) ⇒ Ξ) ×
    (Γ ⊢ drop x ∘ drop y ≡ⱼ drop (y + x) ⇒ Ξ)
dropCompEq {_} { x } {_} {_} { zero } Δ⊢dropX⇒Ξ Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
  in sbStability' ⊢Γ≡Δ Δ⊢dropX⇒Ξ , SbEqIdᵣ Δ⊢dropX⇒Ξ Γ⊢id⇒Δ
dropCompEq {_} { x } {Ξ} {_} { suc y } Δ⊢dropX⇒Ξ (SbDropˢ {Γ} {_} {_} {A} Γ⊢dropY⇒Δ Γ⊢A) = let
    Γ⊢dropY+X⇒Ξ , Γ⊢dropX∘dropY≡dropY+X⇒Ξ = dropCompEq Δ⊢dropX⇒Ξ Γ⊢dropY⇒Δ
    Γ◁A⊢drop1⇒Γ = display Γ⊢A
    Γ◁A⊢drop1+Y+X⇒Ξ = SbDropˢ Γ⊢dropY+X⇒Ξ Γ⊢A
    open SbEqReason
    Γ◁A⊢dropX∘drop1+Y≡drop1+Y+X⇒Ξ = 
      Γ ◁ A ⊢begin-sb
        drop x ∘ drop (1 + y)
      sb-≡⟨ sbEqComp₂ Δ⊢dropX⇒Ξ (SbEqDropComp Γ⊢dropY⇒Δ Γ◁A⊢drop1⇒Γ) ⟨
        drop x ∘ (drop y ∘ drop 1)
      sb-≡⟨ SbEqCompAssoc Δ⊢dropX⇒Ξ Γ⊢dropY⇒Δ Γ◁A⊢drop1⇒Γ ⟨
        drop x ∘ drop y ∘ drop 1
      sb-≡⟨ sbEqComp₁ Γ⊢dropX∘dropY≡dropY+X⇒Ξ Γ◁A⊢drop1⇒Γ ⟩
        drop (y + x) ∘ drop 1
      sb-≡⟨ SbEqDropComp Γ⊢dropY+X⇒Ξ Γ◁A⊢drop1⇒Γ ⟩
        drop (1 + (y + x))
      sb-≡⟨ sbEqDrop Γ◁A⊢drop1+Y+X⇒Ξ refl ⟨∣
        drop (1 + y + x)
      ∎⇒ Ξ
  in Γ◁A⊢drop1+Y+X⇒Ξ , Γ◁A⊢dropX∘drop1+Y≡drop1+Y+X⇒Ξ
dropCompEq {_} { x } {Ξ} {_} { suc y } Δ₂⊢dropX⇒Ξ (SbConv Γ⊢dropSY⇒Δ₁ ⊢Δ₁≡Δ₂) = let
    Δ₁⊢dropX⇒Ξ = sbStability' ⊢Δ₁≡Δ₂ Δ₂⊢dropX⇒Ξ
  in dropCompEq Δ₁⊢dropX⇒Ξ Γ⊢dropSY⇒Δ₁

private
  drop1CompCommu : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop 1 ⇒ Δ
      → Σ[ Δ' ∈ Context ] 
      (Γ ⊢ drop x ⇒ Δ') ×
      (Δ' ⊢ drop 1 ⇒ Ξ) ×
      Γ ⊢ drop x ∘ drop 1 ≡ⱼ drop 1 ∘ drop x ⇒ Ξ
  drop1CompCommu {_} { zero } {Ξ} {Γ} Δ⊢id⇒Ξ Γ⊢drop1⇒Δ = let
      ⊢Δ≡Ξ = idInversion Δ⊢id⇒Ξ
      ⊢Γ = sbWfCtx Γ⊢drop1⇒Δ
      Γ⊢id⇒Γ = SbId ⊢Γ
      Γ⊢drop1⇒Ξ = (SbConv Γ⊢drop1⇒Δ ⊢Δ≡Ξ)
      open SbEqReason
    in Γ , Γ⊢id⇒Γ , Γ⊢drop1⇒Ξ , (
      Γ ⊢begin-sb
        idₛ ∘ drop 1 
      sb-≡⟨ SbEqIdₗ Δ⊢id⇒Ξ Γ⊢drop1⇒Δ ⟩
        drop 1
      sb-≡⟨ SbEqIdᵣ Γ⊢drop1⇒Ξ Γ⊢id⇒Γ ⟨∣
        drop 1 ∘ idₛ
      ∎⇒ Ξ
    )
  drop1CompCommu {Δ} { suc x } {Ξ} {Γ} Δ⊢drop-sx⇒Ξ Γ⊢drop1⇒Δ = let
      dropSucInv Δ₁ A Δ₁⊢A ⊢Δ≡Δ₁◁A Δ₁⊢drop-x⇒Ξ = dropSInversion Δ⊢drop-sx⇒Ξ
      ctxExtInv Γ' A Γ'⊢A ⊢Γ≡Γ'◁A , ⊢Γ'≡Δ = drop1Inversion Γ⊢drop1⇒Δ
      Δ₁◁A⊢drop1⇒Δ₁ = display Δ₁⊢A
      Δ⊢drop1⇒Δ₁ = sbStability' ⊢Δ≡Δ₁◁A Δ₁◁A⊢drop1⇒Δ₁
      Δ₂ , Δ⊢drop-x⇒Δ₂ , Δ₂⊢drop1⇒Ξ , Δ⊢drop-x∘drop-1≡drop-1∘dropx⇒Ξ = drop1CompCommu Δ₁⊢drop-x⇒Ξ Δ⊢drop1⇒Δ₁
      open SbEqReason
      Γ⊢drop-sx⇒Δ₂ = begin
          intro-⟨ Δ⊢drop-x⇒Δ₂ ⟩ Δ ⊢ drop x ⇒ Δ₂  
        ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ'≡Δ ⟩
          Γ' ⊢ drop x ⇒ Δ₂
        ⎯⎯⎯⎯⟨ Sb-Dropₛ-ext Γ'⊢A ⟩
          Γ' ◁ A ⊢ drop (1 + x) ⇒ Δ₂
        ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ≡Γ'◁A ⟩
          Γ ⊢ drop (1 + x) ⇒ Δ₂
        ∎
    in Δ₂ , Γ⊢drop-sx⇒Δ₂ , Δ₂⊢drop1⇒Ξ , (
      Γ ⊢begin-sb
        drop (1 + x) ∘ drop 1
      sb-≡⟨ sbEqComp₁ (SbEqDropComp Δ₁⊢drop-x⇒Ξ Δ⊢drop1⇒Δ₁) Γ⊢drop1⇒Δ ⟨
        drop x ∘ drop 1 ∘ drop 1 
      sb-≡⟨ sbEqComp₁ Δ⊢drop-x∘drop-1≡drop-1∘dropx⇒Ξ Γ⊢drop1⇒Δ ⟩
        drop 1 ∘ drop x ∘ drop 1 
      sb-≡⟨ SbEqCompAssoc Δ₂⊢drop1⇒Ξ Δ⊢drop-x⇒Δ₂ Γ⊢drop1⇒Δ ⟩
        drop 1 ∘ (drop x ∘ drop 1)
      sb-≡⟨ sbEqComp₂ Δ₂⊢drop1⇒Ξ (SbEqDropComp Δ⊢drop-x⇒Δ₂ Γ⊢drop1⇒Δ) ⟩∣
        drop 1 ∘ drop (1 + x) 
      ∎⇒ Ξ
    )



dropCompCommu : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop y ⇒ Δ
  → Σ[ Δ' ∈ Context ] 
    (Γ ⊢ drop x ⇒ Δ') ×
    (Δ' ⊢ drop y ⇒ Ξ) ×
    Γ ⊢ drop y ∘ drop x ≡ⱼ drop x ∘ drop y ⇒ Ξ
dropCompCommu {_} { x } {Ξ} {Γ} { zero } Δ⊢drop-x⇒Ξ Γ⊢id⇒Δ = let
    ⊢Γ≡Δ = idInversion Γ⊢id⇒Δ
    Ξ⊢id⇒Ξ = SbId (sbWfCodomain Δ⊢drop-x⇒Ξ)
    Γ⊢drop-x⇒Ξ = sbStability' ⊢Γ≡Δ Δ⊢drop-x⇒Ξ
    open SbEqReason
  in Ξ , Γ⊢drop-x⇒Ξ , Ξ⊢id⇒Ξ , (
    Γ ⊢begin-sb
      idₛ ∘ drop x  
    sb-≡⟨ SbEqIdₗ Ξ⊢id⇒Ξ Γ⊢drop-x⇒Ξ ⟩
      drop x
    sb-≡⟨ SbEqIdᵣ Δ⊢drop-x⇒Ξ Γ⊢id⇒Δ ⟨∣
      drop x ∘ idₛ
    ∎⇒ Ξ
  )
dropCompCommu {_} { x } {Ξ} {Γ} { suc y } Δ⊢drop-x⇒Ξ Γ⊢drop-sy⇒Δ = let
    dropSucInv Γ₁ A Γ₁⊢A ⊢Γ≡Γ₁◁A Γ₁⊢drop-y⇒Δ = dropSInversion Γ⊢drop-sy⇒Δ
    Δ₁ , Γ₁⊢drop-x⇒Δ₁ , Δ₁⊢drop-y⇒Ξ , Γ₁⊢drop-y∘drop-x≡drop-x∘drop-y⇒Ξ 
      = dropCompCommu Δ⊢drop-x⇒Ξ Γ₁⊢drop-y⇒Δ
    Γ⊢drop1⇒Γ₁ = sbStability' ⊢Γ≡Γ₁◁A (display Γ₁⊢A)
    Γ₂ , Γ⊢drop-x⇒Γ₂ , Γ₂⊢drop1⇒Δ₁ , Γ⊢drop-x∘drop1≡drop1∘dropx⇒Δ₁ 
      = drop1CompCommu Γ₁⊢drop-x⇒Δ₁ Γ⊢drop1⇒Γ₁
    ctxExtInv Γ₃ B Γ₃⊢B ⊢Γ₂≡Γ₃◁B , ⊢Γ₃≡Δ₁ = drop1Inversion Γ₂⊢drop1⇒Δ₁
    Γ₂⊢drop-sy⇒Ξ = 
      begin
        intro-⟨ Δ₁⊢drop-y⇒Ξ ⟩ Δ₁  ⊢ drop y ⇒ Ξ  
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ₃≡Δ₁ ⟩
        Γ₃  ⊢ drop y ⇒ Ξ
      ⎯⎯⎯⎯⟨ Sb-Dropₛ-ext Γ₃⊢B ⟩
        Γ₃ ◁ B ⊢ drop (1 + y) ⇒ Ξ
      ⎯⎯⎯⎯⟨ Sb-Stability' ⊢Γ₂≡Γ₃◁B ⟩
        Γ₂ ⊢ drop (1 + y) ⇒ Ξ
      ∎
    open SbEqReason
  in Γ₂ , Γ⊢drop-x⇒Γ₂ , Γ₂⊢drop-sy⇒Ξ , (
    Γ ⊢begin-sb
      drop (1 + y) ∘ drop x
    sb-≡⟨ sbEqComp₁ (SbEqDropComp Δ₁⊢drop-y⇒Ξ Γ₂⊢drop1⇒Δ₁) Γ⊢drop-x⇒Γ₂ ⟨
      drop y ∘ drop 1 ∘ drop x
    sb-≡⟨ SbEqCompAssoc Δ₁⊢drop-y⇒Ξ Γ₂⊢drop1⇒Δ₁ Γ⊢drop-x⇒Γ₂ ⟩
      drop y ∘ (drop 1 ∘ drop x)
    sb-≡⟨ sbEqComp₂ Δ₁⊢drop-y⇒Ξ Γ⊢drop-x∘drop1≡drop1∘dropx⇒Δ₁ ⟨
      drop y ∘ (drop x ∘ drop 1)
    sb-≡⟨ SbEqCompAssoc Δ₁⊢drop-y⇒Ξ Γ₁⊢drop-x⇒Δ₁ Γ⊢drop1⇒Γ₁ ⟨
      drop y ∘ drop x ∘ drop 1
    sb-≡⟨ sbEqComp₁ Γ₁⊢drop-y∘drop-x≡drop-x∘drop-y⇒Ξ Γ⊢drop1⇒Γ₁ ⟩
      drop x ∘ drop y ∘ drop 1
    sb-≡⟨ SbEqCompAssoc Δ⊢drop-x⇒Ξ Γ₁⊢drop-y⇒Δ Γ⊢drop1⇒Γ₁ ⟩
      drop x ∘ (drop y ∘ drop 1)
    sb-≡⟨ sbEqComp₂ Δ⊢drop-x⇒Ξ (SbEqDropComp Γ₁⊢drop-y⇒Δ Γ⊢drop1⇒Γ₁) ⟩∣
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
    dropSucInv Γ' B Γ'⊢B ⊢Γ≡Γ'◁B Γ'⊢dropY⇒Δ = dropSInversion Γ⊢dropSY⇒Δ
    Γ⊢drop1⇒Γ' = sbStability' ⊢Γ≡Γ'◁B (display Γ'⊢B)
    in begin
      intro-⟨ liftVar Δ⊢A Δ⊢VarX∷A Γ'⊢dropY⇒Δ ⟩ Γ' ⊢ Var (y + x) ∷ A [ drop y ]ₑ 
    ⎯⎯⎯⎯⟨ Tm-Var-ext Γ'⊢B ⟩
      Γ' ◁ B ⊢ Var (1 + (y + x)) ∷ A [ drop y ]ₑ [ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-Stability' ⊢Γ≡Γ'◁B ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop y ]ₑ [ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-TyConv-by (TyEqSubstSubst Δ⊢A Γ'⊢dropY⇒Δ Γ⊢drop1⇒Γ') ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop y ∘ drop 1 ]ₑ
    ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ⊢A (SbEqDropComp Γ'⊢dropY⇒Δ Γ⊢drop1⇒Γ')) ⟩
      Γ ⊢ Var (1 + (y + x)) ∷ A [ drop (1 + y) ]ₑ
    ∎ 

sbExpand : Γ ⊢ γ ⇒ Δ ◁ A
    → Γ ⊢ γ ≡ⱼ (drop 1 ∘ γ) ◀ Var 0 [ γ ]ₑ ⇒ (Δ ◁ A)
sbExpand {Γ} {γ} {Δ} {A} Γ⊢γ⇒Δ◁A = let
    ⊢Δ◁A = sbWfCodomain Γ⊢γ⇒Δ◁A
    ⊢Δ , Δ⊢A = ctxExtInversion ⊢Δ◁A
    Δ◁A⊢Var0∷A[drop1] = TmVarᶻ Δ⊢A
    Δ◁A⊢drop1⇒Δ = display Δ⊢A
    Δ◁A⊢drop1◀Var0⇒Δ◁A = SbExt Δ◁A⊢drop1⇒Δ Δ⊢A Δ◁A⊢Var0∷A[drop1]
    Δ◁A⊢drop1◀Var0≡id⇒Δ◁A = SbEqExtVar Δ◁A⊢Var0∷A[drop1]
    open SbEqReason
  in 
    Γ ⊢begin-sb
        γ
      sb-≡⟨ SbEqIdₗ (SbId ⊢Δ◁A) Γ⊢γ⇒Δ◁A ⟨
        idₛ ∘ γ
      sb-≡⟨ sbEqComp₁ Δ◁A⊢drop1◀Var0≡id⇒Δ◁A Γ⊢γ⇒Δ◁A ⟨
        drop 1 ◀ Var 0 ∘ γ
      sb-≡⟨ SbEqExtComp Δ◁A⊢drop1◀Var0⇒Δ◁A  Γ⊢γ⇒Δ◁A ⟩∣
        (drop 1 ∘ γ) ◀ Var 0 [ γ ]ₑ
      ∎⇒ Δ ◁ A


liftSectionCommute : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Δ ⊢ a ∷ A
    → Γ ⊢ lift γ ∘ idₛ ◀ a [ γ ]ₑ ≡ⱼ idₛ ◀ a ∘ γ ⇒ Δ ◁ A
liftSectionCommute {Γ} {γ} {Δ} {A} {a} Γ⊢γ⇒Δ Δ⊢A Δ⊢a∷A = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    ⊢Δ = tyWfCtx Δ⊢A
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ⊢a[γ]∷A[γ] = TmSubst Δ⊢a∷A Γ⊢γ⇒Δ
    Γ◁A[γ]⊢liftγ⇒Δ◁A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ⊢id◀a[γ]⇒Γ◁A[γ] = section Γ⊢A[γ] Γ⊢a[γ]∷A[γ]
    Γ◁A[γ]⊢drop1⇒Γ = display Γ⊢A[γ]
    Γ⊢A[γ][drop1][id◀a[γ]] = TySubst (TySubst Γ⊢A[γ] Γ◁A[γ]⊢drop1⇒Γ) Γ⊢id◀a[γ]⇒Γ◁A[γ]
    Δ⊢id◀a⇒Δ◁A = section Δ⊢A Δ⊢a∷A
    open SbEqReason
    open TmHEqReason
    Γ⊢γ∘drop1∘id◀a[γ]≡id∘γ⇒Δ = 
      Γ ⊢begin-sb
        γ ∘ drop 1 ∘ idₛ ◀ a [ γ ]ₑ
      sb-≡⟨ SbEqCompAssoc Γ⊢γ⇒Δ Γ◁A[γ]⊢drop1⇒Γ Γ⊢id◀a[γ]⇒Γ◁A[γ] ⟩
        γ ∘ (drop 1 ∘ idₛ ◀ a [ γ ]ₑ)
      sb-≡⟨ sbEqComp₂ Γ⊢γ⇒Δ (SbEqDropExt Γ◁A[γ]⊢drop1⇒Γ Γ⊢id◀a[γ]⇒Γ◁A[γ]) ⟩
        γ ∘ idₛ
      sb-≡⟨ SbEqIdᵣ Γ⊢γ⇒Δ (SbId ⊢Γ) ⟩
        γ
      sb-≡⟨ SbEqIdₗ (SbId ⊢Δ) Γ⊢γ⇒Δ ⟨∣
        idₛ ∘ γ
      ∎⇒ Δ
      
    Γ⊢a[γ]≡Var0[id◀a[γ]]∷A[γ∘drop1∘id◀a[id∘γ]] = 
      Γ ⊢begin-heqₗ
        a [ γ ]ₑ ∷ (A [ idₛ ∘ γ ]ₑ)
      heq-≡⟨∷ tyEqSubst₂ Δ⊢A Γ⊢γ∘drop1∘id◀a[γ]≡id∘γ⇒Δ ∷⟨
        a [ γ ]ₑ  ∷ A [ γ ∘ drop 1 ∘ idₛ ◀ a [ γ ]ₑ ]ₑ
      heq-≡⟨∷ tyEq3Sb Δ⊢A Γ⊢γ⇒Δ Γ◁A[γ]⊢drop1⇒Γ Γ⊢id◀a[γ]⇒Γ◁A[γ] ∷⟨
        a [ γ ]ₑ  ∷ A [ γ ]ₑ [ drop 1 ]ₑ [ idₛ ◀ a [ γ ]ₑ ]ₑ
      heq-≡⟨ TmEqSubstVarExt (TmVarᶻ Γ⊢A[γ]) Γ⊢id◀a[γ]⇒Γ◁A[γ] ⟨∣ Γ⊢A[γ][drop1][id◀a[γ]] ∣
        Var 0 [ idₛ ◀ a [ γ ]ₑ ]ₑ ∷ A [ γ ]ₑ [ drop 1 ]ₑ [ idₛ ◀ a [ γ ]ₑ ]ₑ
      ∎
  in
    Γ ⊢begin-sb
      lift γ ∘ idₛ ◀ a [ γ ]ₑ
    sb-≡⟨⟩
      ((γ ∘ drop 1) ◀ Var 0) ∘ idₛ ◀ a [ γ ]ₑ
    sb-≡⟨ SbEqExtComp Γ◁A[γ]⊢liftγ⇒Δ◁A Γ⊢id◀a[γ]⇒Γ◁A[γ] ⟩
      (γ ∘ drop 1 ∘ idₛ ◀ a [ γ ]ₑ) ◀ (Var 0 [ idₛ ◀ a [ γ ]ₑ ]ₑ)
    sb-≡⟨ SbEqExt (SbEqSym Γ⊢γ∘drop1∘id◀a[γ]≡id∘γ⇒Δ) Δ⊢A Γ⊢a[γ]≡Var0[id◀a[γ]]∷A[γ∘drop1∘id◀a[id∘γ]] ⟨ -- sym hack
      (idₛ ∘ γ) ◀ a [ γ ]ₑ
    sb-≡⟨ SbEqExtComp Δ⊢id◀a⇒Δ◁A Γ⊢γ⇒Δ ⟨∣
      idₛ ◀ a ∘ γ
    ∎⇒ Δ ◁ A

--- 

liftDropEq : Γ ⊢ A
    → Γ ◁ A ⊢ lift (drop 1) ∘ idₛ ◀ (Var 0) ≡ⱼ idₛ ⇒ Γ ◁ A
liftDropEq {Γ} {A} Γ⊢A = let
    ⊢Γ◁A = ctxExt Γ⊢A
    Γ◁A⊢drop1⇒Γ = display Γ⊢A
    Γ◁A⊢A[drop1] = TySubst Γ⊢A Γ◁A⊢drop1⇒Γ
    Γ◁A⊢var0∷A[drop1] = TmVarᶻ Γ⊢A
    Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] = section Γ◁A⊢A[drop1] Γ◁A⊢var0∷A[drop1]
    Γ◁A◁A[drop1]⊢drop1⇒Γ◁A = display Γ◁A⊢A[drop1]
    Γ◁A◁A[drop1]⊢lift[drop1]⇒Γ◁A = liftSb Γ◁A⊢drop1⇒Γ Γ⊢A
    Γ◁A◁A[drop1]⊢Var0∷A[drop1][drop1] = TmVarᶻ Γ◁A⊢A[drop1]
    open SbEqReason
    open TmHEqReason
    Γ◁A⊢drop2∘id◀Var0≡drop1⇒Γ = 
      Γ ◁ A ⊢begin-sb
        drop 1 ∘ drop 1 ∘ idₛ ◀ Var 0
      sb-≡⟨ SbEqCompAssoc Γ◁A⊢drop1⇒Γ Γ◁A◁A[drop1]⊢drop1⇒Γ◁A Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] ⟩
        drop 1 ∘ (drop 1 ∘ idₛ ◀ Var 0)
      sb-≡⟨ sbEqComp₂ Γ◁A⊢drop1⇒Γ (SbEqDropExt Γ◁A◁A[drop1]⊢drop1⇒Γ◁A Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1]) ⟩
        drop 1 ∘ idₛ
      sb-≡⟨ SbEqIdᵣ Γ◁A⊢drop1⇒Γ (SbId ⊢Γ◁A) ⟩∣
        drop 1
      ∎⇒ Γ
    
    Γ◁A⊢Var0≡Var0[id◀var0]∷A[drop1] = 
      Γ ◁ A ⊢begin-heqᵣ
        Var 0 [ idₛ ◀ Var 0 ]ₑ ∷ A [ drop 1 ]ₑ [ drop 1 ]ₑ [ idₛ ◀ Var 0 ]ₑ
      heq-≡⟨ TmEqSubstVarExt Γ◁A◁A[drop1]⊢Var0∷A[drop1][drop1] Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] ⟩
        Var 0   ∷ A [ drop 1 ]ₑ [ drop 1 ]ₑ [ idₛ ◀ Var 0 ]ₑ
      heq-≡⟨∷ tyEq3Sb Γ⊢A Γ◁A⊢drop1⇒Γ Γ◁A◁A[drop1]⊢drop1⇒Γ◁A Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] ∷⟩
        Var 0   ∷ A [ drop 1 ∘ drop 1 ∘ idₛ ◀ Var 0 ]ₑ
      heq-≡⟨∷ tyEqSubst₂ Γ⊢A Γ◁A⊢drop2∘id◀Var0≡drop1⇒Γ  ∷⟩∣ 
        Γ◁A⊢var0∷A[drop1] 
      ⟩∎∷ A [ drop 1 ]ₑ
  in 
    Γ ◁ A ⊢begin-sb
      lift (drop 1) ∘ idₛ ◀ Var 0
    sb-≡⟨⟩
      (drop 1 ∘ drop 1) ◀ Var 0 ∘ idₛ ◀ Var 0
    sb-≡⟨ SbEqExtComp Γ◁A◁A[drop1]⊢lift[drop1]⇒Γ◁A Γ◁A⊢id◀var0⇒Γ◁A◁A[drop1] ⟩
      (drop 1 ∘ drop 1 ∘ idₛ ◀ Var 0) ◀ Var 0 [ idₛ ◀ Var 0 ]ₑ
    sb-≡⟨ SbEqExt (SbEqSym Γ◁A⊢drop2∘id◀Var0≡drop1⇒Γ) Γ⊢A (TmEqSym Γ◁A⊢Var0≡Var0[id◀var0]∷A[drop1]) ⟨ -- sym hack
      drop 1 ◀ Var 0
    sb-≡⟨ SbEqExtVar Γ◁A⊢var0∷A[drop1] ⟩∣
      idₛ
    ∎⇒ Γ ◁ A

liftDropComm : Γ ⊢ γ ⇒ Δ → Δ ⊢ A
    → Γ ◁ A [ γ ]ₑ ⊢ drop 1 ∘ lift γ ≡ⱼ γ ∘ drop 1 ⇒ Δ
liftDropComm {Γ} {γ} {Δ} {A} Γ⊢γ⇒Δ Δ⊢A = let
    Δ◁A⊢drop1⇒Δ = display Δ⊢A
    open SbEqReason
  in 
    Γ ◁ A [ γ ]ₑ ⊢begin-sb
      drop 1 ∘ lift γ
    sb-≡⟨⟩
      drop 1 ∘ (γ ∘ drop 1) ◀ Var 0
    sb-≡⟨ SbEqDropExt Δ◁A⊢drop1⇒Δ (liftSb Γ⊢γ⇒Δ Δ⊢A) ⟩∣
      γ ∘ drop 1
    ∎⇒ Δ

liftComm : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Δ ◁ A ⊢ a ∷ A [ drop 1 ]ₑ
    → Γ ◁ A [ γ ]ₑ ⊢ (drop 1 ◀ a) ∘ lift γ ≡ⱼ lift γ ∘ (drop 1 ◀ a [ lift γ ]ₑ) ⇒ Δ ◁ A
liftComm {Γ} {γ} {Δ} {A} {a} Γ⊢γ⇒Δ Δ⊢A Δ◁A⊢a∷A[drop1] = let
    Γ⊢A[γ] = TySubst Δ⊢A Γ⊢γ⇒Δ
    
    Δ◁A⊢drop1⇒Δ = display Δ⊢A
    Δ◁A⊢drop1◀a⇒Δ◁A = SbExt Δ◁A⊢drop1⇒Δ Δ⊢A Δ◁A⊢a∷A[drop1]
    Γ◁A[γ]⊢lift-γ⇒Δ◁A = liftSb Γ⊢γ⇒Δ Δ⊢A
    Γ◁A[γ]⊢drop1⇒Γ = display Γ⊢A[γ]
    Γ◁A[γ]⊢Var0∷A[γ][drop1] = TmVarᶻ Γ⊢A[γ]

    Γ◁A[γ]⊢A[drop1][lift-γ]≡A[drop1∘lift-γ] = TyEqSubstSubst Δ⊢A Δ◁A⊢drop1⇒Δ Γ◁A[γ]⊢lift-γ⇒Δ◁A

    Γ◁A[γ]⊢a[lift-γ]∷A[drop1∘lift-γ] = 
      begin
        intro-⟨ Δ◁A⊢a∷A[drop1] ⟩
        Δ ◁ A ⊢ a ∷ A [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-Subst-by Γ◁A[γ]⊢lift-γ⇒Δ◁A ⟩
        Γ ◁ A [ γ ]ₑ ⊢ a [ lift γ ]ₑ ∷ A [ drop 1 ]ₑ [ lift γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by Γ◁A[γ]⊢A[drop1][lift-γ]≡A[drop1∘lift-γ] ⟩
        Γ ◁ A [ γ ]ₑ ⊢ a [ lift γ ]ₑ ∷ A [ drop 1 ∘ lift γ ]ₑ
      ∎

    Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ] =
      begin
        intro-⟨ Γ◁A[γ]⊢a[lift-γ]∷A[drop1∘lift-γ] ⟩
        Γ ◁ A [ γ ]ₑ ⊢ (a [ lift γ ]ₑ) ∷ A [ drop 1 ∘ lift γ ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by (tyEqSubst₂ Δ⊢A (liftDropComm Γ⊢γ⇒Δ Δ⊢A)) ⟩
        Γ ◁ A [ γ ]ₑ ⊢ a [ lift γ ]ₑ ∷ A [ γ ∘ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Tm-TyConv-by' (TyEqSubstSubst Δ⊢A Γ⊢γ⇒Δ Γ◁A[γ]⊢drop1⇒Γ) ⟩
        Γ ◁ A [ γ ]ₑ ⊢ a [ lift γ ]ₑ ∷ A [ γ ]ₑ [ drop 1 ]ₑ
      ⎯⎯⎯⎯⟨ Sb-Ext-to Γ◁A[γ]⊢drop1⇒Γ Γ⊢A[γ] ⟩
        Γ ◁ A [ γ ]ₑ ⊢ drop 1 ◀ a [ lift γ ]ₑ ⇒ Γ ◁ A [ γ ]ₑ
      ∎
    open SbEqReason
    baseEq = Γ ◁ A [ γ ]ₑ ⊢begin-sb
        drop 1 ∘ lift γ
      sb-≡⟨ liftDropComm Γ⊢γ⇒Δ Δ⊢A ⟩
        γ ∘ drop 1
      sb-≡⟨ sbEqComp₂ Γ⊢γ⇒Δ (SbEqDropExt Γ◁A[γ]⊢drop1⇒Γ Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ]) ⟨
        γ ∘ (drop 1 ∘ (drop 1 ◀ a [ lift γ ]ₑ))
      sb-≡⟨ SbEqCompAssoc Γ⊢γ⇒Δ Γ◁A[γ]⊢drop1⇒Γ Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ] ⟨∣
        γ ∘ drop 1 ∘ (drop 1 ◀ a [ lift γ ]ₑ)
      ∎⇒ Δ
    open TmHEqReason
    tmEq =  
      Γ ◁ A [ γ ]ₑ ⊢begin-heqᵣ
        Var 0 [ drop 1 ◀ a [ lift γ ]ₑ ]ₑ  ∷  A  [ γ ]ₑ [ drop 1 ]ₑ [ drop 1 ◀ a [ lift γ ]ₑ ]ₑ
      heq-≡⟨ TmEqSubstVarExt Γ◁A[γ]⊢Var0∷A[γ][drop1] Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ] ⟩ -- 
        a [ lift γ ]ₑ  ∷  A  [ γ ]ₑ [ drop 1 ]ₑ [ drop 1 ◀ a [ lift γ ]ₑ ]ₑ
      heq-≡⟨∷  tyEq3Sb Δ⊢A Γ⊢γ⇒Δ Γ◁A[γ]⊢drop1⇒Γ Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ]  ∷⟩
        a [ lift γ ]ₑ  ∷  A  [ γ ∘ drop 1 ∘ (drop 1 ◀ a [ lift γ ]ₑ) ]ₑ
      heq-≡⟨∷  tyEqSubst₂ Δ⊢A baseEq  ∷⟨∣ 
        Γ◁A[γ]⊢a[lift-γ]∷A[drop1∘lift-γ]
      ⟩∎∷ A [ drop 1 ∘ lift γ ]ₑ

  in Γ ◁ A [ γ ]ₑ ⊢begin-sb
      drop 1 ◀ a ∘ lift γ
    sb-≡⟨ SbEqExtComp Δ◁A⊢drop1◀a⇒Δ◁A Γ◁A[γ]⊢lift-γ⇒Δ◁A ⟩
      (drop 1 ∘ lift γ) ◀ a [ lift γ ]ₑ
    sb-≡⟨ SbEqExt baseEq Δ⊢A (TmEqSym tmEq)  ⟩
      (γ ∘ drop 1 ∘ (drop 1 ◀ a [ lift γ ]ₑ)) ◀ (Var 0 [ drop 1 ◀ a [ lift γ ]ₑ ]ₑ)
    sb-≡⟨ SbEqExtComp Γ◁A[γ]⊢lift-γ⇒Δ◁A Γ◁A[γ]⊢drop1◀a[lift-γ]⇒Γ◁A[γ] ⟨∣
      lift γ ∘ (drop 1 ◀ a [ lift γ ]ₑ)
    ∎⇒ Δ ◁ A

drop2SucExpEq : Γ ◁ Nat ⊢ A 
  → Γ ◁ Nat ◁ A ⊢ drop 2 ◀ Succ (Var 1) ≡ⱼ drop 1 ◀ Succ (Var 0) ∘ drop 1 ⇒ Γ ◁ Nat
drop2SucExpEq {Γ} {A} Γ◁ℕ⊢A = let
    ⊢Γ◁ℕ = tyWfCtx Γ◁ℕ⊢A
    ⊢Γ , Γ⊢ℕ = ctxExtInversion ⊢Γ◁ℕ
    Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ = display Γ◁ℕ⊢A
    Γ◁ℕ⊢drop1⇒Γ = display Γ⊢ℕ
    Γ◁ℕ⊢Var0∷ℕ = natVarᶻ ⊢Γ
    Γ◁ℕ⊢SVar0∷ℕ = TmSucc Γ◁ℕ⊢Var0∷ℕ
    Γ◁ℕ⊢drop1◀SVar0⇒Γ◁ℕ = sbExtNat Γ◁ℕ⊢drop1⇒Γ Γ◁ℕ⊢SVar0∷ℕ
    open SbEqReason
    open TmHEqReason
    Γ◁ℕ◁A⊢SVar0[drop1]≡SVar1∷ℕ[drop1∘drop1] = 
      Γ ◁ Nat ◁ A ⊢begin-heqₗ
        (Succ (Var 0)) [ drop 1 ]ₑ  ∷ Nat [ drop 1 ∘ drop 1 ]ₑ
      heq-≡⟨∷  TyEqNatSubst (SbComp Γ◁ℕ⊢drop1⇒Γ Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ)  ∷⟩
       ( Succ (Var 0)) [ drop 1 ]ₑ  ∷ Nat
      heq-≡⟨ TmEqSuccSubst Γ◁ℕ⊢SVar0∷ℕ Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ ⟩
        Succ (Var 0 [ drop 1 ]ₑ)  ∷ Nat
      heq-≡⟨ TmEqSucc (TmEqConv (TmEqSubstVarDrop Γ◁ℕ⊢Var0∷ℕ Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ) (TyEqNatSubst Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ)) ⟩∣ 
        TyNat (ctxExt Γ◁ℕ⊢A) ∣
        Succ (Var 1)  ∷ Nat
      ∎
  in 
    Γ ◁ Nat ◁ A ⊢begin-sb
      drop 2 ◀ Succ (Var 1)
    sb-≡⟨ SbEqExt (SbEqDropComp Γ◁ℕ⊢drop1⇒Γ  Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ) Γ⊢ℕ Γ◁ℕ◁A⊢SVar0[drop1]≡SVar1∷ℕ[drop1∘drop1] ⟨
      (drop 1 ∘ drop 1) ◀ Succ (Var 0) [ drop 1 ]ₑ 
    sb-≡⟨ SbEqExtComp  Γ◁ℕ⊢drop1◀SVar0⇒Γ◁ℕ Γ◁ℕ◁A⊢drop1⇒Γ◁ℕ ⟨∣
      drop 1 ◀ Succ (Var 0) ∘ drop 1
    ∎⇒ Γ ◁ Nat

drop2Ext2Eq : Γ ⊢ γ ◀ a ◀ b ⇒ Δ ◁ A ◁ B
    → Γ ⊢ drop 2 ∘ γ ◀ a ◀ b ≡ⱼ γ ⇒ Δ
drop2Ext2Eq {Γ} {γ} {a} {b} {Δ} {A} {B} Γ⊢γ◀a◀b⇒Δ◁A◁B = let
    ⊢Δ◁A , Δ◁A⊢B = ctxExtInversion (sbWfCodomain Γ⊢γ◀a◀b⇒Δ◁A◁B)
    ⊢Δ , Δ⊢A = ctxExtInversion ⊢Δ◁A
    Γ⊢γ◀a⇒Δ◁A , Γ⊢b∷B[γ◀a] = sbExtInversion' Γ⊢γ◀a◀b⇒Δ◁A◁B
    Γ⊢γ⇒Δ , Γ⊢a∷A[γ] = sbExtInversion' Γ⊢γ◀a⇒Δ◁A

    open SbEqReason
  in 
    Γ ⊢begin-sb
      drop 2 ∘ γ ◀ a ◀ b
    sb-≡⟨ sbEqComp₁ (SbEqDropComp (display Δ⊢A) (display Δ◁A⊢B)) Γ⊢γ◀a◀b⇒Δ◁A◁B ⟨
      drop 1 ∘ drop 1 ∘ γ ◀ a ◀ b 
    sb-≡⟨ SbEqCompAssoc (display Δ⊢A) (display Δ◁A⊢B) Γ⊢γ◀a◀b⇒Δ◁A◁B ⟩
      drop 1 ∘ (drop 1 ∘ γ ◀ a ◀ b) 
    sb-≡⟨ sbEqComp₂ (display Δ⊢A) (SbEqDropExt (display Δ◁A⊢B) Γ⊢γ◀a◀b⇒Δ◁A◁B) ⟩
      drop 1 ∘ γ ◀ a 
    sb-≡⟨ SbEqDropExt (display Δ⊢A) Γ⊢γ◀a⇒Δ◁A ⟩∣
      γ
    ∎⇒ Δ


varSbˢ : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Δ ⊢ Var x ∷ A → Δ ⊢ B → Γ ⊢ b ∷ B [ γ ]ₑ → Γ ⊢ Var x [ γ ]ₑ ≡ⱼ a ∷ A [ γ ]ₑ 
  → Γ ⊢ Var (1 + x) [ γ ◀ b ]ₑ ≡ⱼ a ∷ A [ γ ]ₑ
varSbˢ {Γ} {γ} {Δ} {A}  {x} {B} {b} {a} Γ⊢γ⇒Δ Δ⊢A Δ⊢Var-x∷A Δ⊢B Γ⊢b∷B[γ] Γ⊢Var-x[γ]≡a∷A = let
    Γ⊢γ◀b⇒Δ◁B = SbExt Γ⊢γ⇒Δ Δ⊢B Γ⊢b∷B[γ]
    Δ◁B⊢drop1⇒Δ = display Δ⊢B
    Δ◁B⊢A[drop1] = TySubst Δ⊢A Δ◁B⊢drop1⇒Δ
    open TmHEqReason
  in 
    Γ ⊢begin-heqᵣ
      Var (1 + x) [ γ ◀ b ]ₑ ∷ A [ drop 1 ]ₑ [ γ ◀ b ]ₑ
    heq-≡⟨∣ hTmEqSubst₁ (hTmEqFund' Δ◁B⊢A[drop1] (TmEqSubstVarDrop Δ⊢Var-x∷A Δ◁B⊢drop1⇒Δ)) Γ⊢γ◀b⇒Δ◁B  ∙⟩
      Var x [ drop 1 ]ₑ [ γ ◀ b ]ₑ ∷ A [ drop 1 ]ₑ [ γ ◀ b ]ₑ
    heq-≡⟨∣ hTmEqSubstSubst Δ◁B⊢drop1⇒Δ Γ⊢γ◀b⇒Δ◁B Δ⊢A Δ⊢Var-x∷A  ∙⟩
      Var x [ drop 1 ∘ γ ◀ b ]ₑ ∷ A [ drop 1 ∘ γ ◀ b ]ₑ
    heq-≡⟨∣ hTmEqSubst₂ Δ⊢A Δ⊢Var-x∷A (SbEqDropExt Δ◁B⊢drop1⇒Δ  Γ⊢γ◀b⇒Δ◁B) ∙⟩
      Var x [ γ ]ₑ ∷ A [ γ ]ₑ
    heq-≡⟨ Γ⊢Var-x[γ]≡a∷A ⟩∣ TySubst Δ⊢A Γ⊢γ⇒Δ ∣
      a  ∷ A [ γ ]ₑ
    ∎
