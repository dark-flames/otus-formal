{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Inversion.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Utils
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Relation
open import Otus.Syntax.Typed.Presupposition.Reason
open import Otus.Syntax.Typed.Presupposition.Inversion.Base
open import Otus.Syntax.Typed.Presupposition.Inversion.Context

open PropositionalEq
open Product

record VarExistence ( Γ : Context ) ( x : ℕ ) : Set where
  constructor varExist 
  field
    Γ' : Context
    A : Type
    Γ'⊢A : Γ' ⊢ A
    Γ⊢dropSX⇒Γ' : Γ ⊢ drop (suc x) ⇒ Γ'
    Γ⊢dropX⇒Γ'◁A : Γ ⊢ drop x ⇒ Γ' ◁ A

private
  variable
    x : ℕ
    u u₁ : Universe
    Γ : Context
    A B T : Type
    a b c : Term

piTmInversion : Γ ⊢ Pi A B ∷ T
  → Γ ⊢ A × Γ ◁ A ⊢ B
piTmInversion tm with tm
...| TmPi Γ⊢A∈u₁ Γ◁A⊢B∈u₂ = tyRussel Γ⊢A∈u₁ , tyRussel Γ◁A⊢B∈u₂
...| TmCum {_} {_} {u} Γ⊢PiAB∈u = piTmInversion Γ⊢PiAB∈u
...| TmTyConv Γ⊢PiAB∷T _ =  piTmInversion Γ⊢PiAB∷T

varTmInversion : Γ ⊢ Var x ∷ T 
  → Σ[ inv ∈ VarExistence Γ x ]
    Γ ⊢ T ≡ⱼ (VarExistence.A inv) [ drop (suc x) ]ₑ
varTmInversion (TmVarᶻ Γ⊢A) = let 
    Γ◁A⊢drop⇒Γ = display Γ⊢A
    ⊢Γ◁A = ctxExt Γ⊢A
    inv = varExist _ _ Γ⊢A Γ◁A⊢drop⇒Γ (SbId ⊢Γ◁A) 
    Γ◁A⊢A[drop1] = tySubst Γ⊢A Γ◁A⊢drop⇒Γ
  in inv , tyEqRefl Γ◁A⊢A[drop1]
varTmInversion (TmVarˢ {Γ} {x} {T} {B} Γ⊢VarX∷T Γ⊢B) = let 
    Γ◁B⊢drop⇒Γ = display Γ⊢B
    varExist Γ' A Γ'⊢A Γ⊢dropSX⇒Γ' Γ⊢dropX⇒Γ'◁A , Γ⊢T≡A[dropSX] = varTmInversion Γ⊢VarX∷T
    Γ◁B⊢dropSX⇒Γ'◁A = SbDropˢ Γ⊢dropX⇒Γ'◁A Γ⊢B
    Γ◁B⊢dropSSX⇒Γ' = SbDropˢ Γ⊢dropSX⇒Γ' Γ⊢B
    Γ◁B⊢dropSX∘drop⇒Γ' = SbComp Γ⊢dropSX⇒Γ' Γ◁B⊢drop⇒Γ
    inv = varExist Γ' A Γ'⊢A Γ◁B⊢dropSSX⇒Γ' Γ◁B⊢dropSX⇒Γ'◁A
    open TyEqReason
    Γ◁B⊢T[drop1]≡A[dropSSX] = 
      Γ ◁ B ⊢begin-ty
        T [ drop 1 ]ₑ
      ty-≡⟨ tyEqSubst₁ Γ⊢T≡A[dropSX] Γ◁B⊢drop⇒Γ ⟩
        A [ drop (1 + x) ]ₑ [ drop 1 ]ₑ
      ty-≡⟨ tyEqSubstSubst Γ'⊢A Γ⊢dropSX⇒Γ' Γ◁B⊢drop⇒Γ ⟩
        A [ drop (1 + x) ∘ drop 1 ]ₑ
      ty-≡⟨ tyEqSubst₂ Γ'⊢A Γ◁B⊢dropSX∘drop⇒Γ' (SbEqDropComp Γ⊢dropSX⇒Γ' Γ◁B⊢drop⇒Γ) ⟩∣
        A [ drop (2 + x) ]ₑ
      ∎
  in inv , Γ◁B⊢T[drop1]≡A[dropSSX]
varTmInversion (TmCum {_} {_} {u} Γ⊢VarX∈u) = let 
    varExist Γ' A Γ'⊢A Γ⊢dropSX⇒Γ' Γ⊢dropX⇒Γ'◁A , Γ⊢U≡A[dropX] = varTmInversion Γ⊢VarX∈u
    ⊢Γ' = tyWfCtx Γ'⊢A
    ⊢Γ'◁A≡Γ'◁SU = ctxEqExt₂ ⊢Γ' Γ'⊢A (tyUniv ⊢Γ') {!   !}
    Γ⊢dropX⇒Γ'◁SU = SbConv Γ⊢dropX⇒Γ'◁A ⊢Γ'◁A≡Γ'◁SU
    inv = varExist Γ' (Univ (lsuc u)) (tyUniv ⊢Γ') Γ⊢dropSX⇒Γ' Γ⊢dropX⇒Γ'◁SU
  in inv , 
varTmInversion (TmTyConv Γ⊢VarX∷G Γ⊢G≡T) = let
    inv , Γ⊢G≡A[dropX] = varTmInversion Γ⊢VarX∷G
  in inv , (tyEqTrans (tyEqSym Γ⊢G≡T) Γ⊢G≡A[dropX])

succTmInversion : Γ ⊢ Succ a ∷ T → Γ ⊢ a ∷ Nat × (Γ ⊢ T ≡ⱼ Nat)
succTmInversion (TmSucc Γ⊢a∷Nat) = let
    ⊢Γ = tmWfCtx Γ⊢a∷Nat
  in Γ⊢a∷Nat , tyEqRefl (tyNat ⊢Γ)
succTmInversion (TmTyConv Γ⊢Succ-a∷G Γ⊢G≡T) = let
    Γ⊢a∷Nat , Γ⊢G≡Nat = succTmInversion Γ⊢Succ-a∷G
  in Γ⊢a∷Nat , tyEqTrans (tyEqSym Γ⊢G≡T) Γ⊢G≡Nat

natElimTmInversion : Γ ⊢ NatElim A a b c ∷ T 
    → (Γ ◁ Nat ⊢ A) ×
      (Γ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ) ×
      (Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ) × 
      (Γ ⊢ c ∷ Nat) ×
      (Γ ⊢ T ≡ⱼ A [ idₛ ◀ c ]ₑ)
natElimTmInversion (TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ) = let
    ⊢Γ = tmWfCtx Γ⊢c∷ℕ
    Γ⊢id◀c⇒Γ◁ℕ = section (tyNat ⊢Γ) Γ⊢c∷ℕ
    Γ⊢A[id◀c] = tySubst Γ◁ℕ⊢A Γ⊢id◀c⇒Γ◁ℕ
  in Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , tyEqRefl Γ⊢A[id◀c]
natElimTmInversion(TmTyConv Γ⊢ne∷G Γ⊢G≡T) = let
    Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , Γ⊢G≡A[id◀c] = natElimTmInversion Γ⊢ne∷G
  in Γ◁ℕ⊢A , Γ⊢a∷A[id◀Z] , Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] , Γ⊢c∷ℕ , tyEqTrans (tyEqSym Γ⊢G≡T) Γ⊢G≡A[id◀c]

  
{-

univEqLiftCong : Γ ⊢ Univ u₁ ≡ⱼ Univ u₂ ∈ᵤ lsuc u₂
  → Γ ⊢ Univ (lsuc u₁) ≡ⱼ Univ (lsuc u₂) ∈ᵤ liftUniv 2 u₂
univEqLiftCong' : Γ ⊢ Univ u₂ ≡ⱼ Univ u₁ ∈ᵤ lsuc u₂
  → Γ ⊢ Univ (lsuc u₁) ≡ⱼ Univ (lsuc u₂) ∈ᵤ liftUniv 2 u₂

univEqLiftCong eq with eq
...| TmEqSym Γ⊢U₂≡U₁∷SU₂ = univEqLiftCong' Γ⊢U₂≡U₁∷SU
...| TmEqTrans  Γ⊢U₁≡A∷SU₂  Γ⊢A≡U₂∷SU₂

univEqLiftCong' eq with eq
...| TmEqSym Γ⊢U₁≡U₂∷SU₂ = univEqLiftCong Γ⊢U₁≡U₂∷SU₂

piTmInversion : Γ ⊢ Pi A B ∷ T
  → Σ[ u ∈ Universe ]
    (Γ ⊢ T ≡ⱼ Univ u ∷ Univ (lsuc u)) × 
    (Γ ⊢ A ∈ᵤ u) ×
    (Γ ◁ A ⊢ B ∈ᵤ u)
piTmInversion (TmPi Γ⊢A∈u₁ Γ◁A⊢B∈u₂) = let 
    u₁ = univOf Γ⊢A∈u₁
    u₂ = univOf Γ◁A⊢B∈u₂
    ⊢Γ = tmWfCtx Γ⊢A∈u₁
  in u₁ ⊔ᵤ u₂ , tmEqRefl (TmUniv ⊢Γ) , liftTy Γ⊢A∈u₁ u₁⊆u₁⊔u₂ , liftTy Γ◁A⊢B∈u₂ u₂⊆u₁⊔u₂
piTmInversion (TmCum {_} {_} {u₁} Γ⊢PiAB∈u₁) = let 
    u₂ , Γ⊢U₁≡U₂∷SU₂ , Γ⊢A∈u₂ , Γ◁A⊢B∈u₂ = piTmInversion Γ⊢PiAB∈u₁
  in lsuc u₂ , {!   !} , TmCum Γ⊢A∈u₂ , TmCum Γ◁A⊢B∈u₂
piTmInversion (TmTyConv Γ⊢PiAB∷T Γ⊢T≡U) = {!   !}
piTmInversion (TmCum Γ⊢PiAB∈u) = let
    (uLvlConjInv u₁ u₂ u₁₂ u₁⊔u₂≡u₁₂ u₁₂⊆u) , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂ = piTmInversion Γ⊢PiAB∈u
    inv = uLvlConjInv u₁ u₂ u₁₂ u₁⊔u₂≡u₁₂ (⊆-lsucᵣ u₁₂⊆u)
  in inv , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂
piTmInversion (TmTyConv Γ⊢PiAB∷U₂ Γ⊢U₂≡U) = {!   !} let 
    inv , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂ = piTmInversion Γ⊢PiAB∷U₂
  in ? , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂-}
{-
piTmInversion (TmTyConv Γ⊢PiAB∷G Γ⊢G≡T) = let 
    inv , Γ⊢G≡Ul , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂ = piTmInversion Γ⊢PiAB∷G
    Γ⊢T≡Ul = tyEqTrans (tyEqSym Γ⊢G≡T) Γ⊢G≡Ul
  in inv , Γ⊢T≡Ul , Γ⊢A∈u₁ , Γ◁A⊢B∈u₂
  -}

{-

-}