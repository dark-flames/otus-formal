{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.CtxConv where

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
tyCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tmCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
sbCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
tyEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tmEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
sbEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ

-- tyCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A
tyCtxConv ⊢Γ≡ⱼΔ (tyJdg u Γ⊢A∈u) = tyJdg u (tmCtxConv ⊢Γ≡ⱼΔ Γ⊢A∈u)

-- tmCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ∷ A → Δ ⊢ a ∷ A
tmCtxConv (CEqEmp) = id
tmCtxConv (CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarᶻ _) = let 
    Δ◁B⊢Var0∷B = TmVarᶻ Δ⊢B
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡ⱼΔ)
    Δ◁B⇒Δ = SbDropˢ (SbId ⊢Δ) Δ⊢B
    Δ◁B⊢B≡A = tyEqSubst₁ (tyEqSym Δ⊢A≡B) Δ◁B⇒Δ
  in TmTyConv Δ◁B⊢Var0∷B Δ◁B⊢B≡A
tmCtxConv (CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (TmVarˢ Γ⊢VarX∷C _) = let
    Δ⊢VarX∷C = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢VarX∷C 
  in TmVarˢ Δ⊢VarX∷C Δ⊢B
tmCtxConv ⊢Γ≡ⱼΔ (TmPi Γ⊢A∷U Γ◁A⊢B∷U) = let
    Δ⊢A∷U = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢A∷U
    Δ⊢A = tyRussel Δ⊢A∷U
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡ⱼΔ (tyRussel Γ⊢A∷U) Δ⊢A
    Δ◁A⊢B∷U = tmCtxConv ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢B∷U 
  in TmPi Δ⊢A∷U Δ◁A⊢B∷U
tmCtxConv ⊢Γ≡ⱼΔ (TmLam Γ⊢A Γ◁A⊢b∷B) = let 
    Δ⊢A = tyCtxConv ⊢Γ≡ⱼΔ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡ⱼΔ Γ⊢A Δ⊢A
    Δ◁A⊢b∷B = tmCtxConv ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢b∷B
  in TmLam Δ⊢A Δ◁A⊢b∷B
tmCtxConv ⊢Γ≡ⱼΔ (TmApp Γ⊢f∷PiAB Γ⊢a∷A) = let
    Δ⊢f∷PiAB = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢f∷PiAB
    Δ⊢a∷A = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A
  in TmApp Δ⊢f∷PiAB Δ⊢a∷A
tmCtxConv ⊢Γ≡ⱼΔ (TmNat ⊢Γ) = let
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡ⱼΔ)
  in TmNat ⊢Δ
tmCtxConv ⊢Γ≡ⱼΔ (TmZero ⊢Γ) = let
    ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡ⱼΔ)
  in TmZero ⊢Δ
tmCtxConv ⊢Γ≡ⱼΔ (TmSucc Γ⊢a∷Nat) = let
    Δ⊢a∷Nat = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷Nat
  in TmSucc Δ⊢a∷Nat
tmCtxConv ⊢Γ≡ⱼΔ (TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ) = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡ⱼΔ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡ⱼΔ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyCtxConv ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmCtxConv ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
    Δ⊢c∷Nat = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢c∷ℕ
  in TmNatElim Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] Δ⊢c∷Nat
tmCtxConv ⊢Γ≡ⱼΔ (TmSubst Ξ⊢a∷A Γ⊢γ⇒Ξ) = let 
  Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmSubst Ξ⊢a∷A Δ⊢γ⇒Ξ
tmCtxConv ⊢Γ≡ⱼΔ (TmUniv _) = TmUniv (proj₂ (ctxEqWf ⊢Γ≡ⱼΔ))
tmCtxConv ⊢Γ≡ⱼΔ (TmCum Γ⊢A∷U) = TmCum (tmCtxConv ⊢Γ≡ⱼΔ Γ⊢A∷U)
tmCtxConv ⊢Γ≡ⱼΔ (TmTyConv Γ⊢a∷A Γ⊢A≡B) = let 
    Δ⊢a∷A = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A 
    Δ⊢A≡B = tyEqCtxConv ⊢Γ≡ⱼΔ Γ⊢A≡B
  in TmTyConv Δ⊢a∷A Δ⊢A≡B

-- sbCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ δ ⇒ Ξ → Δ ⊢ δ ⇒ Ξ
sbCtxConv CEqEmp = id
sbCtxConv (CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (SbDropˢ Γ⇒Ξ _) = 
  let Δ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⇒Ξ in SbDropˢ Δ⇒Ξ Δ⊢B
sbCtxConv ⊢Γ≡ⱼΔ (SbId ⊢Γ) = let ⊢Δ = proj₂ (ctxEqWf ⊢Γ≡ⱼΔ)
  in SbConv (SbId ⊢Δ) (ctxEqSym ⊢Γ≡ⱼΔ)
sbCtxConv ⊢Γ≡ⱼΔ (SbExt Γ⇒Ξ Ξ⊢A Γ⊢a∷Aγ) = let 
    Δ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⇒Ξ
    Δ⊢a∷Aγ = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷Aγ
  in SbExt Δ⇒Ξ Ξ⊢A Δ⊢a∷Aγ
sbCtxConv ⊢Γ≡ⱼΔ (SbComp Γ₂⇒Γ₃ Γ⇒Γ₂) = let 
    Δ⇒Γ₃ = sbCtxConv ⊢Γ≡ⱼΔ Γ⇒Γ₂
  in SbComp Γ₂⇒Γ₃ Δ⇒Γ₃
sbCtxConv ⊢Γ≡ⱼΔ (SbConv Γ⇒Ξ₁ ⊢Ξ₁≡Ξ₂) = let 
    Δ⇒Ξ₁ = sbCtxConv ⊢Γ≡ⱼΔ Γ⇒Ξ₁
  in SbConv Δ⇒Ξ₁ ⊢Ξ₁≡Ξ₂

-- tyEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Δ ⊢ A ≡ⱼ B
tyEqCtxConv ⊢Γ≡ⱼΔ (tyEqJdg u Γ⊢A≡B∈u) = tyEqJdg u (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢A≡B∈u)

-- tmEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ a ≡ⱼ b ∷ A → Δ ⊢ a ≡ⱼ b ∷ A
tmEqCtxConv ⊢Γ≡ⱼΔ eq with eq
...| TmEqSym Γ⊢b≡a∷A = TmEqSym (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢b≡a∷A)
...| TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a≡b∷A) (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢b≡c∷A)
...| TmEqLam Γ⊢A Γ◁A⊢a≡b∷B = let 
    Δ⊢A = tyCtxConv ⊢Γ≡ⱼΔ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡ⱼΔ Γ⊢A Δ⊢A
    Δ◁A⊢a≡b∷B = tmEqCtxConv ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢a≡b∷B
  in TmEqLam Δ⊢A Δ◁A⊢a≡b∷B
...| TmEqPi Γ⊢A Γ⊢A≡B∷U Γ◁A⊢C≡D∷U = let 
    Δ⊢A≡B∷U = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢A≡B∷U
    Δ⊢A = tyCtxConv ⊢Γ≡ⱼΔ Γ⊢A
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡ⱼΔ Γ⊢A Δ⊢A
    Δ◁A⊢C≡D∷U = tmEqCtxConv ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢C≡D∷U
  in TmEqPi Δ⊢A Δ⊢A≡B∷U Δ◁A⊢C≡D∷U
...| TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = let 
    Δ⊢f≡g∷PiAB = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢f≡g∷PiAB
    Δ⊢a≡b∷A = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a≡b∷A
    Δ⊢PiAB = tyCtxConv ⊢Γ≡ⱼΔ Γ⊢PiAB
  in TmEqApp Δ⊢PiAB Δ⊢f≡g∷PiAB Δ⊢a≡b∷A
...| TmEqSucc Γ⊢a≡b∷Nat = let
    Δ⊢a≡b∷Nat = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a≡b∷Nat
  in TmEqSucc Δ⊢a≡b∷Nat
...| TmEqNatElim Γ◁ℕ⊢A₁ Γ◁ℕ⊢A₁≡A₂ Γ⊢a₁≡a₂∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Γ⊢c₁≡c₂∷Nat = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡ⱼΔ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡ⱼΔ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A₁ = tyCtxConv ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁
    ⊢Γ◁ℕ◁A₁≡ⱼΔ◁ℕ◁A₁ = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁ Δ◁ℕ⊢A₁
    Δ◁ℕ⊢A₁≡A₂ = tyEqCtxConv ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A₁≡A₂
    Δ⊢a₁≡a₂∷A₁[id◀Z] = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a₁≡a₂∷A₁[id◀Z]
    Δ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] = tmEqCtxConv ⊢Γ◁ℕ◁A₁≡ⱼΔ◁ℕ◁A₁ Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1]
    Δ⊢c₁≡c₂∷Nat = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢c₁≡c₂∷Nat
  in TmEqNatElim Δ◁ℕ⊢A₁ Δ◁ℕ⊢A₁≡A₂ Δ⊢a₁≡a₂∷A₁[id◀Z] Δ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Δ⊢c₁≡c₂∷Nat
...| TmEqSubst Ξ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Ξ = let 
    Δ⊢γ₁≡γ₂⇒Ξ = sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₁≡γ₂⇒Ξ
  in TmEqSubst Ξ⊢a≡b∷A Δ⊢γ₁≡γ₂⇒Ξ
...| TmEqCum Γ⊢A≡B∷U = TmEqCum (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢A≡B∷U)
...| TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = let 
    Δ⊢A≡B = tyEqCtxConv ⊢Γ≡ⱼΔ Γ⊢A≡B
    Δ⊢a≡b∷A = tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a≡b∷A
  in TmEqConv Δ⊢a≡b∷A Δ⊢A≡B
...| TmEqSubstId Γ⊢a∷A = let 
    Δ⊢a∷A = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A
  in TmEqSubstId Δ⊢a∷A
...| TmEqSubstVarExt Ξ⊢Var0∷A Γ⊢γ◀a⇒Ξ = let 
    Δ⊢γ◀a⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ◀a⇒Ξ
  in TmEqSubstVarExt Ξ⊢Var0∷A Δ⊢γ◀a⇒Ξ
...| TmEqSubstVarDrop Ξ⊢VarX∷A Γ⊢dropy⇒Ξ = let 
    Δ⊢dropy⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢dropy⇒Ξ
  in TmEqSubstVarDrop Ξ⊢VarX∷A Δ⊢dropy⇒Ξ
...| TmEqLamSubst Ξ⊢lama∷PiAB Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqLamSubst Ξ⊢lama∷PiAB Δ⊢γ⇒Ξ
...| TmEqPiSubst Ξ⊢PiAB∷U Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqPiSubst Ξ⊢PiAB∷U Δ⊢γ⇒Ξ
...| TmEqAppSubst Ξ⊢fa∷A Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqAppSubst Ξ⊢fa∷A Δ⊢γ⇒Ξ
...| TmEqNatSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqNatSubst Δ⊢γ⇒Ξ
...| TmEqZeroSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqZeroSubst Δ⊢γ⇒Ξ
...| TmEqSuccSubst Ξ⊢Succ-a∷ℕ Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqSuccSubst Ξ⊢Succ-a∷ℕ Δ⊢γ⇒Ξ
...| TmEqNatElimSubst Ξ⊢NatElim∷A[id◀c] Γ⊢γ⇒Ξ = let
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqNatElimSubst Ξ⊢NatElim∷A[id◀c] Δ⊢γ⇒Ξ
...| TmEqSubstSubst Θ⊢a∷A Ξ⊢δ⇒Θ Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqSubstSubst Θ⊢a∷A Ξ⊢δ⇒Θ Δ⊢γ⇒Ξ
...| TmEqUSubst Γ⊢γ⇒Ξ = let 
    Δ⊢γ⇒Ξ = sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ
  in TmEqUSubst Δ⊢γ⇒Ξ
...| TmEqPiBeta Γ⊢A Γ◁A⊢b∷B Γ⊢a∷A = let 
    Δ⊢A = tyCtxConv ⊢Γ≡ⱼΔ Γ⊢A 
    ⊢Γ◁A≡ⱼΔ◁A = ctxEqExtRefl ⊢Γ≡ⱼΔ Γ⊢A Δ⊢A
    Δ◁A⊢b∷B = tmCtxConv ⊢Γ◁A≡ⱼΔ◁A Γ◁A⊢b∷B
    Δ⊢a∷A = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A
  in TmEqPiBeta Δ⊢A Δ◁A⊢b∷B Δ⊢a∷A
...| TmEqNatElimZero Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡ⱼΔ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡ⱼΔ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyCtxConv ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmCtxConv ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
  in TmEqNatElimZero Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1]
...| TmEqNatElimSucc Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ = let
    ⊢Γ , ⊢Δ = ctxEqWf ⊢Γ≡ⱼΔ
    ⊢Γ◁ℕ≡ⱼΔ◁ℕ = ctxEqExtRefl ⊢Γ≡ⱼΔ (tyNat ⊢Γ) (tyNat ⊢Δ)
    Δ◁ℕ⊢A = tyCtxConv ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A
    ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A = ctxEqExtRefl ⊢Γ◁ℕ≡ⱼΔ◁ℕ Γ◁ℕ⊢A Δ◁ℕ⊢A
    Δ⊢a∷A[id◀Z] = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢a∷A[id◀Z]
    Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] = tmCtxConv ⊢Γ◁ℕ◁A≡ⱼΔ◁ℕ◁A Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]
    Δ⊢c∷Nat = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢c∷ℕ
  in TmEqNatElimSucc Δ◁ℕ⊢A Δ⊢a∷A[id◀Z] Δ◁ℕ◁A⊢b∷A[drop2◀SVar1] Δ⊢c∷Nat
...| TmEqPiEta Γ⊢f∷PiAB = let 
    Δ⊢f∷PiAB = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢f∷PiAB
  in TmEqPiEta Δ⊢f∷PiAB
...| TmEqNatEta Γ⊢c∷ℕ = let 
    Δ⊢c∷ℕ = tmCtxConv ⊢Γ≡ⱼΔ Γ⊢c∷ℕ
  in TmEqNatEta Δ⊢c∷ℕ

-- sbEqCtxConv : ⊢ Γ ≡ⱼ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ → Δ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Ξ
sbEqCtxConv  ⊢Γ≡ⱼΔ eq with eq
...| SbEqSym Γ⊢γ₂≡γ₁⇒Ξ = SbEqSym (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₂≡γ₁⇒Ξ)
...| SbEqTrans Γ⊢γ₁≡γ₂⇒Ξ  Γ⊢γ₂≡γ₃⇒Ξ  = SbEqTrans (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₁≡γ₂⇒Ξ) (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₂≡γ₃⇒Ξ)
...| SbEqExt Γ⊢γ₁≡γ₂⇒Ξ Ξ⊢A Γ⊢a≡b∷Aγ₁ = SbEqExt (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₁≡γ₂⇒Ξ) Ξ⊢A (tmEqCtxConv ⊢Γ≡ⱼΔ Γ⊢a≡b∷Aγ₁)
...| SbEqComp Ξ⊢δ₁≡δ₂⇒Θ Γ⊢γ₁≡γ₂⇒Ξ = SbEqComp Ξ⊢δ₁≡δ₂⇒Θ (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₁≡γ₂⇒Ξ)
...| SbEqConv Γ⊢γ₁≡γ₂⇒Ξ₁ ⊢Ξ₁≡Ξ₂ = SbEqConv (sbEqCtxConv ⊢Γ≡ⱼΔ Γ⊢γ₁≡γ₂⇒Ξ₁) ⊢Ξ₁≡Ξ₂
...| SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqCompAssoc Ξ₂⊢ξ⇒Ξ₃ Ξ₁⊢δ⇒Ξ₂ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ₁)
...| SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ Γ⊢id⇒Ξ₁ = SbEqIdᵣ Ξ₁⊢γ⇒Ξ₂ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢id⇒Ξ₁)
...| SbEqIdₗ Ξ₁⊢id⇒Ξ₂ Γ⊢γ⇒Ξ₁ = SbEqIdₗ Ξ₁⊢id⇒Ξ₂ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ₁)
...| SbEqExtVar Γ⊢Var0∷A = SbEqConv (SbEqExtVar (tmCtxConv ⊢Γ≡ⱼΔ Γ⊢Var0∷A)) (ctxEqSym ⊢Γ≡ⱼΔ)
...| SbEqDropExt Ξ⊢drop⇒Θ Γ⊢γ◀a⇒Ξ = SbEqDropExt Ξ⊢drop⇒Θ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ◀a⇒Ξ)
...| SbEqDropComp Ξ⊢dropX⇒Θ Γ⊢drop1⇒Ξ = SbEqDropComp Ξ⊢dropX⇒Θ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢drop1⇒Ξ)
...| SbEqExtComp Ξ⊢δ◀a⇒Θ Γ⊢γ⇒Ξ = SbEqExtComp Ξ⊢δ◀a⇒Θ (sbCtxConv ⊢Γ≡ⱼΔ Γ⊢γ⇒Ξ)

ctxConvTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
ctxConvTrans (CEqEmp) ⊢ε≡ⱼΞ = ⊢ε≡ⱼΞ
ctxConvTrans (CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B) (CEqExt ⊢Δ≡ⱼΞ _ Δ⊢C Δ⊢B≡C Ξ⊢B Ξ⊢C Ξ⊢B≡C) = let 
    ⊢Γ≡ⱼΞ = ctxConvTrans ⊢Γ≡ⱼΔ ⊢Δ≡ⱼΞ
    Γ⊢C = tyCtxConv (ctxEqSym ⊢Γ≡ⱼΔ) Δ⊢C
    Ξ⊢A = tyCtxConv ⊢Δ≡ⱼΞ Δ⊢A
    Δ⊢A≡C = tyEqTrans Δ⊢A≡B Δ⊢B≡C
    Γ⊢A≡C = tyEqCtxConv (ctxEqSym ⊢Γ≡ⱼΔ) Δ⊢A≡C 
    Ξ⊢A≡C = tyEqCtxConv ⊢Δ≡ⱼΞ Δ⊢A≡C
  in CEqExt ⊢Γ≡ⱼΞ Γ⊢A Γ⊢C Γ⊢A≡C Ξ⊢A Ξ⊢C Ξ⊢A≡C
