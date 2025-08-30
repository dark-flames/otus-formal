{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Stability where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Relation
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Utils

open Product
open Function

private
  variable
    x : ℕ
    Γ Δ Ξ  : Context
    γ γ₁ γ₂ δ : Substitution
    a b A B : Term

---- Theorems
tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
sbStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ

tyStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A  → Γ ⊢ A
tmStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A → Γ ⊢ a ∷ A
sbStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ δ ⇒ Ξ

tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tmEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
sbEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ

tyEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
tmEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
sbEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ

ctxEqTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ

---- Proofs

-- tyStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tyStability ⊢Γ≡Δ (tyJdg u Γ⊢A∈u) = tyJdg u (tmStability ⊢Γ≡Δ Γ⊢A∈u)

-- tmStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmStability (CEqEmp) = id
tmStability (CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarᶻ _) = let 
    Δ◁B⊢Var0∷B = TmVarᶻ Δ⊢B
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡Δ)
    Δ◁B⇒Δ = SbDropˢ (SbId ⊢Δ) Δ⊢B
    Δ◁B⊢B≡A = tyEqSubst₁ (tyEqSym Δ⊢A≡B) Δ◁B⇒Δ
  in TmTyConv Δ◁B⊢Var0∷B Δ◁B⊢B≡A
tmStability (CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarˢ Γ⊢VarX∷C _) = let
    Δ⊢VarX∷C = tmStability ⊢Γ≡Δ Γ⊢VarX∷C 
  in TmVarˢ Δ⊢VarX∷C Δ⊢B
tmStability ⊢Γ≡Δ (TmPi Γ⊢A∷U Γ◁A⊢B∷U) = let
    Δ⊢A∷U = tmStability ⊢Γ≡Δ Γ⊢A∷U
    Δ⊢A = tyRussel Δ⊢A∷U
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡Δ (tyRussel Γ⊢A∷U) Δ⊢A
    Δ◁A⊢B∷U = tmStability ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢B∷U 
  in TmPi Δ⊢A∷U Δ◁A⊢B∷U
tmStability ⊢Γ≡Δ (TmLam Γ⊢A Γ◁A⊢b∷B) = let 
    Δ⊢A = tyStability ⊢Γ≡Δ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡Δ Γ⊢A Δ⊢A
    Δ◁A⊢b∷B = tmStability ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢b∷B
  in TmLam Δ⊢A Δ◁A⊢b∷B
tmStability ⊢Γ≡Δ (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let
    Δ⊢f∷PiAB = tmStability ⊢Γ≡Δ Γ⊢f∷PiAB
    Δ⊢a∷A = tmStability ⊢Γ≡Δ Γ⊢a∷A
  in TmApp Δ⊢f∷PiAB Δ⊢a∷A
tmStability ⊢Γ≡Δ (TmNat ⊢Γ) = let
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡Δ)
  in TmNat ⊢Δ
tmStability ⊢Γ≡Δ (TmZero ⊢Γ) = let
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡Δ)
  in TmZero ⊢Δ
tmStability ⊢Γ≡Δ (TmSucc Γ⊢a∷Nat) = let
    Δ⊢a∷Nat = tmStability ⊢Γ≡Δ Γ⊢a∷Nat
  in TmSucc Δ⊢a∷Nat
tmStability ⊢Γ≡Δ (TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ) = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡Δ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡Δ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyStability ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmStability ⊢Γ≡Δ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmStability ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
    Δ⊢c∷Nat = tmStability ⊢Γ≡Δ Γ⊢c∷ℕ
  in TmNatElim Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] Δ⊢c∷Nat
tmStability ⊢Γ≡Δ (TmSubst Ξ⊢a∷A Γ⊢γ⇒Ξ) = let 
  Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmSubst Ξ⊢a∷A Δ⊢γ⇒Ξ
tmStability ⊢Γ≡Δ (TmUniv _) = TmUniv (proj₂ (ctxEqWf ⊢Γ≡Δ))
tmStability ⊢Γ≡Δ (TmCum Γ⊢A∷U) = TmCum (tmStability ⊢Γ≡Δ Γ⊢A∷U)
tmStability ⊢Γ≡Δ (TmTyConv Γ⊢a∷A Γ⊢A≡B) = let 
    Δ⊢a∷A = tmStability ⊢Γ≡Δ Γ⊢a∷A 
    Δ⊢A≡B = tyEqStability ⊢Γ≡Δ Γ⊢A≡B
  in TmTyConv Δ⊢a∷A Δ⊢A≡B

-- sbStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
sbStability CEqEmp = id
sbStability (CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (SbDropˢ Γ⇒Ξ _) = 
  let Δ⇒Ξ = sbStability ⊢Γ≡Δ Γ⇒Ξ in SbDropˢ Δ⇒Ξ Δ⊢B
sbStability ⊢Γ≡Δ (SbId ⊢Γ) = let ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡Δ)
  in SbConv (SbId ⊢Δ) (ctxEqSym ⊢Γ≡Δ)
sbStability ⊢Γ≡Δ (SbExt Γ⇒Ξ Ξ⊢A Γ⊢a∷Aγ) = let 
    Δ⇒Ξ = sbStability ⊢Γ≡Δ Γ⇒Ξ
    Δ⊢a∷Aγ = tmStability ⊢Γ≡Δ Γ⊢a∷Aγ
  in SbExt Δ⇒Ξ Ξ⊢A Δ⊢a∷Aγ
sbStability ⊢Γ≡Δ (SbComp Γ₂⇒Γ₃ Γ⇒Γ₂) = let 
    Δ⇒Γ₃ = sbStability ⊢Γ≡Δ Γ⇒Γ₂
  in SbComp Γ₂⇒Γ₃ Δ⇒Γ₃
sbStability ⊢Γ≡Δ (SbConv Γ⇒Ξ₁ ⊢Ξ₁≡Ξ₂) = let 
    Δ⇒Ξ₁ = sbStability ⊢Γ≡Δ Γ⇒Ξ₁
  in SbConv Δ⇒Ξ₁ ⊢Ξ₁≡Ξ₂

-- tyEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqStability ⊢Γ≡Δ (tyEqJdg u Γ⊢A≡B∈u) = tyEqJdg u (tmEqStability ⊢Γ≡Δ Γ⊢A≡B∈u)

-- tmEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
tmEqStability ⊢Γ≡Δ eq with eq
...| TmEqSym Γ⊢b≡a∷A = TmEqSym (tmEqStability ⊢Γ≡Δ Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷A) (tmEqStability ⊢Γ≡Δ Γ⊢b≡c∷A)
...| TmEqLam Γ⊢A Γ◁A⊢a≡b∷B = let 
    Δ⊢A = tyStability ⊢Γ≡Δ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡Δ Γ⊢A Δ⊢A
    Δ◁A⊢a≡b∷B = tmEqStability ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢a≡b∷B
  in TmEqLam Δ⊢A Δ◁A⊢a≡b∷B
...| TmEqPi Γ⊢A Γ⊢A≡B∷U Γ◁A⊢C≡D∷U = let 
    Δ⊢A≡B∷U = tmEqStability ⊢Γ≡Δ Γ⊢A≡B∷U
    Δ⊢A = tyStability ⊢Γ≡Δ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡Δ Γ⊢A Δ⊢A
    Δ◁A⊢C≡D∷U = tmEqStability ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢C≡D∷U
  in TmEqPi Δ⊢A Δ⊢A≡B∷U Δ◁A⊢C≡D∷U
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    Δ⊢f≡g∷PiAB = tmEqStability ⊢Γ≡Δ Γ⊢f≡g∷PiAB
    Δ⊢a≡b∷A = tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷A
    Δ⊢PiAB = tyStability ⊢Γ≡Δ Γ⊢PiAB
  in TmEqApp Δ⊢PiAB Δ⊢f≡g∷PiAB Δ⊢a≡b∷A
...| TmEqSucc Γ⊢a≡b∷Nat = let
    Δ⊢a≡b∷Nat = tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷Nat
  in TmEqSucc Δ⊢a≡b∷Nat
...| TmEqNatElim Γ◁ℕ⊢A₁ Γ◁ℕ⊢A₁≡A₂ Γ⊢a₁≡a₂∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Γ⊢c₁≡c₂∷Nat = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡Δ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡Δ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A₁ = tyStability ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁
    ⊢Γ◁ℕ◁A₁≡ⱼΔ◁ℕ◁A₁ = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁ Δ◁ℕ⊢A₁
    Δ◁ℕ⊢A₁≡A₂ = tyEqStability ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁≡A₂
    Δ⊢a₁≡a₂∷A₁[id◀Z] = tmEqStability ⊢Γ≡Δ Γ⊢a₁≡a₂∷A₁[id◀Z]
    Δ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] = tmEqStability ⊢Γ◁ℕ◁A₁≡ⱼΔ◁ℕ◁A₁ Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1]
    Δ⊢c₁≡c₂∷Nat = tmEqStability ⊢Γ≡Δ Γ⊢c₁≡c₂∷Nat
  in TmEqNatElim Δ◁ℕ⊢A₁ Δ◁ℕ⊢A₁≡A₂ Δ⊢a₁≡a₂∷A₁[id◀Z] Δ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Δ⊢c₁≡c₂∷Nat
...| TmEqSubst Ξ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Ξ = let 
    Δ⊢γ₁≡γ₂⇒Ξ = sbEqStability ⊢Γ≡Δ Γ⊢γ₁≡γ₂⇒Ξ
  in TmEqSubst Ξ⊢a≡b∷A Δ⊢γ₁≡γ₂⇒Ξ
...| TmEqCum Γ⊢A≡B∷U = TmEqCum (tmEqStability ⊢Γ≡Δ Γ⊢A≡B∷U)
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let 
    Δ⊢A≡B = tyEqStability ⊢Γ≡Δ Γ⊢A≡B
    Δ⊢a≡b∷A = tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷A
  in TmEqConv Δ⊢a≡b∷A Δ⊢A≡B
...| TmEqSubstId Γ⊢a∷A = let 
    Δ⊢a∷A = tmStability ⊢Γ≡Δ Γ⊢a∷A
  in TmEqSubstId Δ⊢a∷A
...| TmEqSubstVarExt Ξ⊢Var0∷A Γ⊢γ◀a⇒Ξ = let 
    Δ⊢γ◀a⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ◀a⇒Ξ
  in TmEqSubstVarExt Ξ⊢Var0∷A Δ⊢γ◀a⇒Ξ
...| TmEqSubstVarDrop Ξ⊢VarX∷A Γ⊢dropy⇒Ξ = let 
    Δ⊢dropy⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢dropy⇒Ξ
  in TmEqSubstVarDrop Ξ⊢VarX∷A Δ⊢dropy⇒Ξ
...| TmEqLamSubst Ξ⊢lama∷PiAB Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqLamSubst Ξ⊢lama∷PiAB Δ⊢γ⇒Ξ
...| TmEqPiSubst Ξ⊢PiAB∷U Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqPiSubst Ξ⊢PiAB∷U Δ⊢γ⇒Ξ
...| TmEqAppSubst Ξ⊢fa∷A Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqAppSubst Ξ⊢fa∷A Δ⊢γ⇒Ξ
...| TmEqNatSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqNatSubst Δ⊢γ⇒Ξ
...| TmEqZeroSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqZeroSubst Δ⊢γ⇒Ξ
...| TmEqSuccSubst Ξ⊢Succ-a∷ℕ Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqSuccSubst Ξ⊢Succ-a∷ℕ Δ⊢γ⇒Ξ
...| TmEqNatElimSubst Ξ⊢NatElim∷A[id◀c] Γ⊢γ⇒Ξ = let
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqNatElimSubst Ξ⊢NatElim∷A[id◀c] Δ⊢γ⇒Ξ
...| TmEqSubstSubst Θ⊢a∷A Ξ⊢δ⇒Θ Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqSubstSubst Θ⊢a∷A Ξ⊢δ⇒Θ Δ⊢γ⇒Ξ
...| TmEqUSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ
  in TmEqUSubst Δ⊢γ⇒Ξ
...| TmEqPiBeta Γ⊢A Γ◁A⊢b∷B Γ⊢a∷A = let 
    Δ⊢A = tyStability ⊢Γ≡Δ Γ⊢A 
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡Δ Γ⊢A Δ⊢A
    Δ◁A⊢b∷B = tmStability ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢b∷B
    Δ⊢a∷A = tmStability ⊢Γ≡Δ Γ⊢a∷A
  in TmEqPiBeta Δ⊢A Δ◁A⊢b∷B Δ⊢a∷A
...| TmEqNatElimZero Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡Δ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡Δ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyStability ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmStability ⊢Γ≡Δ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmStability ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
  in TmEqNatElimZero Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1]
...| TmEqNatElimSucc Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡Δ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡Δ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyStability ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmStability ⊢Γ≡Δ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmStability ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
    Δ⊢c∷Nat = tmStability ⊢Γ≡Δ Γ⊢c∷ℕ
  in TmEqNatElimSucc Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] Δ⊢c∷Nat
...| TmEqPiEta Γ⊢f∷PiAB = let 
    Δ⊢f∷PiAB = tmStability ⊢Γ≡Δ Γ⊢f∷PiAB
  in TmEqPiEta Δ⊢f∷PiAB
...| TmEqNatEta Γ⊢c∷ℕ = let 
    Δ⊢c∷ℕ = tmStability ⊢Γ≡Δ Γ⊢c∷ℕ
  in TmEqNatEta Δ⊢c∷ℕ

-- sbEqStability : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
sbEqStability  ⊢Γ≡Δ eq with eq
...| SbEqSym Γ⊢γ₂≡γ₁⇒Ξ = SbEqSym (sbEqStability ⊢Γ≡Δ Γ⊢γ₂≡γ₁⇒Ξ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Ξ  Γ⊢γ₂≡γ₃⇒Ξ  = SbEqTrans (sbEqStability ⊢Γ≡Δ Γ⊢γ₁≡γ₂⇒Ξ) (sbEqStability ⊢Γ≡Δ Γ⊢γ₂≡γ₃⇒Ξ)
...| SbEqExt Γ⊢γ₁≡γ₂⇒Ξ Ξ⊢A Γ⊢a≡b∷Aγ₁ = SbEqExt (sbEqStability ⊢Γ≡Δ Γ⊢γ₁≡γ₂⇒Ξ) Ξ⊢A (tmEqStability ⊢Γ≡Δ Γ⊢a≡b∷Aγ₁)
...| SbEqComp Ξ⊢δ₁≡δ₂⇒Θ Γ⊢γ₁≡γ₂⇒Ξ = SbEqComp Ξ⊢δ₁≡δ₂⇒Θ (sbEqStability ⊢Γ≡Δ Γ⊢γ₁≡γ₂⇒Ξ)
...| SbEqConv Γ⊢γ₁≡γ₂⇒Ξ₁ ⊢Ξ₁≡Ξ₂ = SbEqConv (sbEqStability ⊢Γ≡Δ Γ⊢γ₁≡γ₂⇒Ξ₁) ⊢Ξ₁≡Ξ₂
...| SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ (sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ₁)
...| SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ Γ⊢id⇒Ξ₁ = SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ (sbStability ⊢Γ≡Δ Γ⊢id⇒Ξ₁)
...| SbEqIdₗ Ξ₁⊢id⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqIdₗ Ξ₁⊢id⇒Ξ₂ (sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ₁)
...| SbEqExtVar Γ⊢Var0∷A = SbEqConv (SbEqExtVar (tmStability ⊢Γ≡Δ Γ⊢Var0∷A)) (ctxEqSym ⊢Γ≡Δ)
...| SbEqDropExt Ξ⊢drop⇒Θ Γ⊢γ◀a⇒Ξ = SbEqDropExt Ξ⊢drop⇒Θ (sbStability ⊢Γ≡Δ Γ⊢γ◀a⇒Ξ)
...| SbEqDropComp Ξ⊢dropX⇒Θ Γ⊢drop1⇒Ξ = SbEqDropComp Ξ⊢dropX⇒Θ (sbStability ⊢Γ≡Δ Γ⊢drop1⇒Ξ)
...| SbEqExtComp Ξ⊢δ◀a⇒Θ Γ⊢γ⇒Ξ = SbEqExtComp Ξ⊢δ◀a⇒Θ (sbStability ⊢Γ≡Δ Γ⊢γ⇒Ξ)

-- ctxEqTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
ctxEqTrans (CEqEmp) ⊢ε≡ⱼΞ = ⊢ε≡ⱼΞ
ctxEqTrans (CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (CEqExt ⊢Δ≡ⱼΞ _ Δ⊢C Δ⊢B≡C Ξ⊢B Ξ⊢C Ξ⊢B≡C) = let 
    ⊢Γ≡ⱼΞ = ctxEqTrans ⊢Γ≡Δ ⊢Δ≡ⱼΞ
    Γ⊢C = tyStability' ⊢Γ≡Δ Δ⊢C
    Ξ⊢A = tyStability ⊢Δ≡ⱼΞ Δ⊢A
    Δ⊢A≡C = tyEqTrans Δ⊢A≡B Δ⊢B≡C
    Γ⊢A≡C = tyEqStability' ⊢Γ≡Δ Δ⊢A≡C 
    Ξ⊢A≡C = tyEqStability ⊢Δ≡ⱼΞ Δ⊢A≡C
  in CEqExt ⊢Γ≡ⱼΞ Γ⊢A Γ⊢C Γ⊢A≡C Ξ⊢A Ξ⊢C Ξ⊢A≡C

-- tyStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A  → Γ ⊢ A
tyStability' ⊢Γ≡Δ = tyStability (ctxEqSym ⊢Γ≡Δ)
-- tmStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ∷ A → Γ ⊢ a ∷ A
tmStability' ⊢Γ≡Δ = tmStability (ctxEqSym ⊢Γ≡Δ)
-- sbStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ δ ⇒ Ξ
sbStability' ⊢Γ≡Δ = sbStability (ctxEqSym ⊢Γ≡Δ)

-- tyEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
tyEqStability' ⊢Γ≡Δ = tyEqStability (ctxEqSym ⊢Γ≡Δ)
-- tmEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
tmEqStability' ⊢Γ≡Δ = tmEqStability (ctxEqSym ⊢Γ≡Δ)
-- sbEqStability' : ⊢ Γ ≡ⱼ Δ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
sbEqStability' ⊢Γ≡Δ = sbEqStability (ctxEqSym ⊢Γ≡Δ)
