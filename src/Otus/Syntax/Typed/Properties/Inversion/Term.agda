{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Context
open import Otus.Syntax.Typed.Properties.Reason

open PropositionalEq
open Product

record ULevelConjInversion : Set where
  constructor uLvlConjInv
  field
    l l₁ l₂ : ULevel
    l₁⊔l₂≡l : l₁ ⊔ l₂ ≡ l

record VarExistence ( Γ : Context ) ( x : ℕ ) : Set where
  constructor varExist 
  field
    Γ' : Context
    A : Term
    Γ'⊢A : Γ' ⊢ A
    Γ⊢dropSX⇒Γ' : Γ ⊢ drop (suc x) ⇒ Γ'
    Γ⊢dropX⇒Γ'◁A : Γ ⊢ drop x ⇒ Γ' ◁ A

private
  variable
    x : ℕ
    Γ : Context
    A B T a b c : Term

piTmInversion : Γ ⊢ Pi A B ∷ T 
  → Σ[ inv ∈ ULevelConjInversion ] 
    (Γ ⊢ T ≡ⱼ Univ (ULevelConjInversion.l inv)) ×
    (Γ ⊢ A ∷ Univ (ULevelConjInversion.l₁ inv)) ×
    (Γ ◁ A ⊢ B ∷ Univ (ULevelConjInversion.l₂ inv))
piTmInversion (TmPi Γ⊢A∷Ul₁ Γ◁A⊢B∷Ul₂) = let 
    l₁ = univInversion Γ⊢A∷Ul₁
    l₂ = univInversion Γ◁A⊢B∷Ul₂
    ⊢Γ = tmWfCtx Γ⊢A∷Ul₁
    inv = uLvlConjInv (l₁ ⊔ l₂) l₁ l₂ refl
  in inv , TyEqRefl (TyUniv ⊢Γ) , Γ⊢A∷Ul₁ , Γ◁A⊢B∷Ul₂
piTmInversion (TmTyConv Γ⊢PiAB∷G Γ⊢G≡T) = let 
    inv , Γ⊢G≡Ul , Γ⊢A∷Ul₁ , Γ◁A⊢B∷Ul₂ = piTmInversion Γ⊢PiAB∷G
    Γ⊢T≡Ul = TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡Ul
  in inv , Γ⊢T≡Ul , Γ⊢A∷Ul₁ , Γ◁A⊢B∷Ul₂

varTmInversion : Γ ⊢ Var x ∷ T 
  → Σ[ inv ∈ VarExistence Γ x ]
    Γ ⊢ T ≡ⱼ (VarExistence.A inv) [ drop (suc x) ]ₑ
varTmInversion (TmVarᶻ Γ⊢A) = let 
    Γ◁A⊢drop⇒Γ = display Γ⊢A
    ⊢Γ◁A = ctxExt Γ⊢A
    inv = varExist _ _ Γ⊢A Γ◁A⊢drop⇒Γ (SbId ⊢Γ◁A) 
    Γ◁A⊢A[drop1] = TySubst Γ⊢A Γ◁A⊢drop⇒Γ
  in inv , TyEqRefl Γ◁A⊢A[drop1]
varTmInversion (TmVarˢ {Γ} {x} {T} {B} Γ⊢VarX∷T Γ⊢B) = let 
    Γ◁B⊢drop⇒Γ = display Γ⊢B
    varExist Γ' A Γ'⊢A Γ⊢dropSX⇒Γ' Γ⊢dropX⇒Γ'◁A , Γ⊢T≡A[dropSX] = varTmInversion Γ⊢VarX∷T
    Γ◁B⊢dropSX⇒Γ'◁A = SbDropˢ Γ⊢dropX⇒Γ'◁A Γ⊢B
    Γ◁B⊢dropSSX⇒Γ' = SbDropˢ Γ⊢dropSX⇒Γ' Γ⊢B
    inv = varExist Γ' A Γ'⊢A Γ◁B⊢dropSSX⇒Γ' Γ◁B⊢dropSX⇒Γ'◁A
    open TyEqReason
    Γ◁B⊢T[drop1]≡A[dropSSX] = 
      Γ ◁ B ⊢begin-ty
        T [ drop 1 ]ₑ
      ty-≡⟨ tyEqSubst₁ Γ⊢T≡A[dropSX] Γ◁B⊢drop⇒Γ ⟩
        A [ drop (1 + x) ]ₑ [ drop 1 ]ₑ
      ty-≡⟨ TyEqSubstSubst Γ'⊢A Γ⊢dropSX⇒Γ' Γ◁B⊢drop⇒Γ ⟩
        A [ drop (1 + x) ∘ drop 1 ]ₑ
      ty-≡⟨ tyEqSubst₂ Γ'⊢A (SbEqDropComp Γ⊢dropSX⇒Γ' Γ◁B⊢drop⇒Γ) ⟩∣
        A [ drop (2 + x) ]ₑ
      ∎
  in inv , Γ◁B⊢T[drop1]≡A[dropSSX]
varTmInversion (TmTyConv Γ⊢VarX∷G Γ⊢G≡T) = let
    inv , Γ⊢G≡A[dropX] = varTmInversion Γ⊢VarX∷G
  in inv , (TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡A[dropX])

succTmInversion : Γ ⊢ Succ a ∷ T → Γ ⊢ a ∷ Nat × (Γ ⊢ T ≡ⱼ Nat)
succTmInversion (TmSucc Γ⊢a∷Nat) = let
    ⊢Γ = tmWfCtx Γ⊢a∷Nat
  in Γ⊢a∷Nat , TyEqRefl (TyNat ⊢Γ)
succTmInversion (TmTyConv Γ⊢Succ-a∷G Γ⊢G≡T) = let
    Γ⊢a∷Nat , Γ⊢G≡Nat = succTmInversion Γ⊢Succ-a∷G
  in Γ⊢a∷Nat , TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡Nat

natElimTmInversion : Γ ⊢ NatElim A a b c ∷ T 
    → (Γ ◁ Nat ⊢ A) ×
      (Γ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ) ×
      (Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ) × 
      (Γ ⊢ c ∷ Nat) ×
      (Γ ⊢ T ≡ⱼ A [ idₛ ◀ c ]ₑ)
natElimTmInversion (TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ) = let
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    Γ⊢id◀c⇒Γ◁ℕ = section (TyNat ⊢Γ) Γ⊢c∷ℕ
    Γ⊢A[id◀c] = TySubst Γ◁ℕ⊢A Γ⊢id◀c⇒Γ◁ℕ
  in Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , TyEqRefl Γ⊢A[id◀c]
natElimTmInversion(TmTyConv Γ⊢ne∷G Γ⊢G≡T) = let
    Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , Γ⊢G≡A[id◀c] = natElimTmInversion Γ⊢ne∷G
  in Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , TyEqTrans (TyEqSym Γ⊢G≡T) Γ⊢G≡A[id◀c]
