{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Utils.Subst where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Utils.Context


private
  variable
    x y : ℕ
    Γ  Δ Ξ : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    A B a b : Term

--- Substitution

display : Γ ⊢ A → Γ ◁ A ⊢ drop 1 ⇒ Γ
display Γ⊢A = let 
    ⊢Γ = tyWfCtx Γ⊢A
  in SbDropˢ (SbId ⊢Γ) Γ⊢A

section : Γ ⊢ A → Γ ⊢ a ∷ A → Γ ⊢ idₛ ◀ a ⇒ Γ ◁ A
section Γ⊢A Γ⊢a∷A = let 
    ⊢Γ = tyWfCtx Γ⊢A
    Γ⊢A[id]≡A = TyEqSubstId Γ⊢A
    Γ⊢a∷A[id] = TmTyConv Γ⊢a∷A (TyEqSym Γ⊢A[id]≡A)
  in SbExt (SbId ⊢Γ) Γ⊢A Γ⊢a∷A[id]

sectionEq : Γ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ idₛ ◀ a ≡ⱼ idₛ ◀ b ⇒ Γ ◁ A
sectionEq Γ⊢A Γ⊢a≡b∷A = let 
    ⊢Γ = tyWfCtx Γ⊢A
    Γ⊢A[id]≡A = TyEqSubstId Γ⊢A
    Γ⊢a≡b∷A[id] = TmEqConv Γ⊢a≡b∷A (TyEqSym Γ⊢A[id]≡A)
  in SbEqExt (SbEqRefl (SbId ⊢Γ)) Γ⊢A Γ⊢a≡b∷A[id]

natVarᶻ : ⊢ Γ  → Γ ◁ Nat ⊢ Var 0 ∷ Nat
natVarᶻ ⊢Γ = let
    Γ⊢ℕ = TyNat ⊢Γ
  in TmTyConv (TmVarᶻ Γ⊢ℕ) (TyEqNatSubst (display Γ⊢ℕ))

natVarˢ : Γ ⊢ Var x ∷ Nat → Γ ⊢ A
    → Γ ◁ A ⊢ Var (suc x) ∷ Nat
natVarˢ Γ⊢Var-x∷ℕ Γ⊢A = TmTyConv (TmVarˢ Γ⊢Var-x∷ℕ Γ⊢A) (TyEqNatSubst (display Γ⊢A))

drop2 : Γ ⊢ A → Γ ◁ A ⊢ B → Γ ◁ A ◁ B ⊢ drop 2 ⇒ Γ
drop2 Γ⊢A Γ◁A⊢B = SbDropˢ (display Γ⊢A) Γ◁A⊢B

liftSb : Γ ⊢ γ ⇒ Δ → Δ ⊢ A 
  → Γ ◁ (A [ γ ]ₑ) ⊢ lift γ ⇒ Δ ◁ A
liftSb Γ⊢γ⇒Δ Δ⊢A = let 
    Γ⊢Aγ = TySubst Δ⊢A Γ⊢γ⇒Δ
    Γ◁Aγ⊢drop1⇒Γ = display Γ⊢Aγ
    Γ◁Aγ⊢γ∘drop1⇒Δ = SbComp Γ⊢γ⇒Δ Γ◁Aγ⊢drop1⇒Γ
    Γ◁Aγ⊢Aγdrop≡A[γ∘drop] = TyEqSubstSubst Δ⊢A Γ⊢γ⇒Δ Γ◁Aγ⊢drop1⇒Γ
    Γ◁Aγ⊢Var0∷↑A = TmTyConv (TmVarᶻ Γ⊢Aγ) Γ◁Aγ⊢Aγdrop≡A[γ∘drop]
  in SbExt Γ◁Aγ⊢γ∘drop1⇒Δ Δ⊢A Γ◁Aγ⊢Var0∷↑A


--- Substition Pairtial Congruence
sbEqExt : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ∷ A [ γ₁ ]ₑ
    → Γ ⊢ γ₁ ◀ a ≡ⱼ γ₂ ◀ a  ⇒ Δ ◁ A
sbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a∷A[γ₁] = SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A (TmEqRefl Γ⊢a∷A[γ₁])

sbEqExt₂ : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A [ γ ]ₑ 
    → Γ ⊢ γ ◀ a ≡ⱼ γ ◀ b  ⇒ Δ ◁ A
sbEqExt₂ Γ⊢γ⇒Δ Δ⊢A Γ⊢a≡b∷A[γ₁] = SbEqExt (SbEqRefl Γ⊢γ⇒Δ) Δ⊢A Γ⊢a≡b∷A[γ₁]

sbEqExt₁ : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ∷ A [ γ₁ ]ₑ 
    → Γ ⊢ γ₁ ◀ a ≡ⱼ γ₂ ◀ a  ⇒ Δ ◁ A
sbEqExt₁ Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a∷A[γ₁] = SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A (TmEqRefl Γ⊢a∷A[γ₁])

sbEqDrop : Γ ⊢ drop x ⇒ Δ → x ≡ y → Γ ⊢ drop x ≡ⱼ drop y ⇒ Δ
sbEqDrop Γ⊢dropX⇒Δ refl = SbEqRefl Γ⊢dropX⇒Δ

sbEqComp₁ : Δ ⊢ δ₁ ≡ⱼ δ₂ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Γ ⊢ δ₁ ∘ γ ≡ⱼ δ₂ ∘ γ ⇒ Ξ
sbEqComp₁ Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ⇒Δ = SbEqComp Δ⊢δ₁≡δ₂⇒Ξ (SbEqRefl Γ⊢γ⇒Δ)

sbEqComp₂ : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ δ ∘ γ₁ ≡ⱼ δ ∘ γ₂ ⇒ Ξ
sbEqComp₂ Δ⊢δ⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = SbEqComp (SbEqRefl Δ⊢δ⇒Ξ) Γ⊢γ₁≡γ₂⇒Δ