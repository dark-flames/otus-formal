{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Fund where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Inversion
open import Otus.Syntax.Typed.Presupposition.Relation
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Utils
open import Otus.Syntax.Typed.Presupposition.Stability

import Otus.Syntax.Typed.Base as T

open Product

private
  variable
    Γ Δ : Context
    A B : Type
    a b : Term
    γ γ₁ γ₂  : Substitution


ctxFund : T.⊢ Γ → ⊢ Γ 
tyFund  : Γ T.⊢ A → Γ ⊢ A 
tmFund  : Γ T.⊢ a ∷ A → Γ ⊢ a ∷ A 
sbFund  : Γ T.⊢ γ ⇒ Δ → Γ ⊢ γ ⇒ Δ

tyEqFund  : Γ T.⊢ A ≡ⱼ B → Γ ⊢ A ≡ⱼ B
ctxEqFund : T.⊢ Γ ≡ⱼ Δ → ⊢ Γ ≡ⱼ Δ
tmEqFund  : Γ T.⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ≡ⱼ b ∷ A
sbEqFund  : Γ T.⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ

ctxFund ctx with ctx
...| T.CEmp = CEmp
...| T.CExt ⊢Γ Γ⊢A = CExt (ctxFund ⊢Γ) (tyFund Γ⊢A)

tyFund (T.tyJdg u Γ⊢A∈u) = tyJdg u (tmFund Γ⊢A∈u)

tmFund tm with tm
...| T.TmVarᶻ Γ⊢A = TmVarᶻ (tyFund Γ⊢A)
...| T.TmVarˢ Γ⊢varX∷A Γ⊢B = TmVarˢ (tmFund Γ⊢varX∷A) (tyFund Γ⊢B)
...| T.TmPi Γ⊢A∈u₁ Γ◁A⊢B∈u₁ = TmPi (tmFund Γ⊢A∈u₁) (tmFund Γ◁A⊢B∈u₁)
...| T.TmLam Γ◁A⊢b∷B = let
    Γ◁A⊢b∷B' = tmFund Γ◁A⊢b∷B
    ⊢Γ◁A = tmWfCtx Γ◁A⊢b∷B'
    _ , Γ⊢A = ctxExtInversion ⊢Γ◁A
  in TmLam Γ⊢A Γ◁A⊢b∷B'
...| T.TmApp Γ⊢f∷PiAB Γ⊢a∷A = TmApp (tmFund Γ⊢f∷PiAB) (tmFund Γ⊢a∷A)
...| T.TmNat ⊢Γ = TmNat (ctxFund ⊢Γ)
...| T.TmZero ⊢Γ = TmZero (ctxFund ⊢Γ)
...| T.TmSucc Γ⊢a∷ℕ = TmSucc (tmFund Γ⊢a∷ℕ)
...| T.TmNatElim Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ = 
  TmNatElim (tyFund Γ◁ℕ⊢A)
            (tmFund Γ⊢a∷A[id◀Z])
            (tmFund Γ◁ℕ◁A⊢b∷A[drop2◀SVar1])
            (tmFund Γ⊢c∷ℕ)
...| T.TmSubst Δ⊢a∷A Γ⊢γ⇒Δ = TmSubst (tmFund Δ⊢a∷A) (sbFund Γ⊢γ⇒Δ)
...| T.TmUniv ⊢Γ = TmUniv (ctxFund ⊢Γ)
...| T.TmCum Γ⊢A∈u = TmCum (tmFund Γ⊢A∈u)
...| T.TmTyConv Γ⊢a∷A Γ⊢A≡B = TmTyConv (tmFund Γ⊢a∷A) (tyEqFund Γ⊢A≡B)

sbFund sb with sb
...| T.SbId ⊢Γ = SbId (ctxFund ⊢Γ)
...| T.SbDropˢ Γ⊢dropX⇒Δ Γ⊢A = SbDropˢ (sbFund Γ⊢dropX⇒Δ) (tyFund Γ⊢A)
...| T.SbExt Γ⊢γ⇒Δ Δ⊢A Γ⊢a∷Aγ = SbExt (sbFund Γ⊢γ⇒Δ) (tyFund Δ⊢A) (tmFund Γ⊢a∷Aγ)
...| T.SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = SbComp (sbFund Δ⊢δ⇒Ξ) (sbFund Γ⊢γ⇒Δ)
...| T.SbConv Γ⊢γ⇒Δ₁ ⊢Δ₁≡Δ₂ = SbConv (sbFund Γ⊢γ⇒Δ₁) (ctxEqFund ⊢Δ₁≡Δ₂)

ctxEqFund ctxEq with ctxEq
...| T.CEqRefl ⊢Γ = ctxEqRefl (ctxFund ⊢Γ)
...| T.CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢B Γ⊢A≡B = CEqExt (ctxEqFund ⊢Γ≡Δ) (tyFund Γ⊢A) (tyFund Γ⊢B) (tyEqFund Γ⊢A≡B)
  (tyStability (ctxEqFund ⊢Γ≡Δ) (tyFund Γ⊢A)) (tyStability (ctxEqFund ⊢Γ≡Δ) (tyFund Γ⊢B)) (tyEqStability (ctxEqFund ⊢Γ≡Δ) (tyEqFund Γ⊢A≡B))

tyEqFund (T.tyEqJdg u Γ⊢A≡B∈u) = tyEqJdg u (tmEqFund Γ⊢A≡B∈u)

tmEqFund eq with eq
-- Eq
...| T.TmEqSym Γ⊢b≡a∷A = TmEqSym (tmEqFund Γ⊢b≡a∷A)
...| T.TmEqTrans Γ⊢a≡b∷A Γ⊢b≡c∷A = TmEqTrans (tmEqFund Γ⊢a≡b∷A) (tmEqFund Γ⊢b≡c∷A)
-- Congruence
...| T.TmEqLam Γ◁A⊢a≡b∷B = let
    Γ◁A⊢a≡b∷B' = tmEqFund Γ◁A⊢a≡b∷B
    ⊢Γ◁A = tmEqWfCtx Γ◁A⊢a≡b∷B'
    _ , Γ⊢A = ctxExtInversion ⊢Γ◁A
  in TmEqLam Γ⊢A Γ◁A⊢a≡b∷B'
...| T.TmEqPi Γ⊢A≡B∷U Γ◁A⊢C≡D∷U = let
    Γ⊢A≡B∷U' = tmEqFund Γ⊢A≡B∷U
    Γ◁A⊢C≡D∷U' = tmEqFund Γ◁A⊢C≡D∷U
    ⊢Γ = tmEqWfCtx Γ⊢A≡B∷U'
  in TmEqPi {!   !} Γ⊢A≡B∷U' Γ◁A⊢C≡D∷U'
...| T.TmEqApp Γ⊢PiAB Γ⊢f≡g∷PiAB Γ⊢a≡b∷A = TmEqApp (tyFund Γ⊢PiAB) (tmEqFund Γ⊢f≡g∷PiAB) (tmEqFund Γ⊢a≡b∷A)
...| T.TmEqSucc Γ⊢a≡b∷Nat = TmEqSucc (tmEqFund Γ⊢a≡b∷Nat)
...| T.TmEqNatElim Γ◁ℕ⊢A₁≡A₂ Γ⊢a₁≡a₂∷A₁[id◀Z] Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1] Γ⊢c₁≡c₂∷Nat = let
    Γ◁ℕ⊢A₁≡A₂' = tyEqFund Γ◁ℕ⊢A₁≡A₂
    ⊢Γ◁ℕ = tyEqWfCtx Γ◁ℕ⊢A₁≡A₂'
    _ , Γ◁ℕ⊢A₁ = ctxExtInversion ⊢Γ◁ℕ
  in TmEqNatElim {!   !} Γ◁ℕ⊢A₁≡A₂' (tmEqFund Γ⊢a₁≡a₂∷A₁[id◀Z]) (tmEqFund Γ◁ℕ◁A₁⊢b₁≡b₂∷A₁[drop2◀SVar1]) (tmEqFund Γ⊢c₁≡c₂∷Nat)
...| T.TmEqSubst Δ⊢a≡b∷A Γ⊢γ₁≡γ₂⇒Δ = TmEqSubst (tmEqFund Δ⊢a≡b∷A) (sbEqFund Γ⊢γ₁≡γ₂⇒Δ)
...| T.TmEqCum Γ⊢A≡B∷U = TmEqCum (tmEqFund Γ⊢A≡B∷U)
...| T.TmEqConv Γ⊢a≡b∷A Γ⊢A≡B = TmEqConv (tmEqFund Γ⊢a≡b∷A) (tyEqFund Γ⊢A≡B)
-- Subst Computation
...| T.TmEqSubstId Γ⊢a∷A = TmEqSubstId (tmFund Γ⊢a∷A)
...| T.TmEqSubstVarExt Δ⊢Var0∷A Γ⊢γ◀a⇒Δ = TmEqSubstVarExt (tmFund Δ⊢Var0∷A) (sbFund Γ⊢γ◀a⇒Δ)
...| T.TmEqSubstVarDrop Δ⊢VarX∷A Γ⊢dropY⇒Δ = TmEqSubstVarDrop (tmFund Δ⊢VarX∷A) (sbFund Γ⊢dropY⇒Δ)
...| T.TmEqLamSubst Δ⊢Lama∷PiAB Γ⊢γ⇒Δ = TmEqLamSubst (tmFund Δ⊢Lama∷PiAB) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqPiSubst Δ⊢PiAB∷U Γ⊢γ⇒Δ = TmEqPiSubst (tmFund Δ⊢PiAB∷U) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqAppSubst Δ⊢fa∷A Γ⊢γ⇒Δ = TmEqAppSubst (tmFund Δ⊢fa∷A) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqNatSubst Γ⊢γ⇒Δ = TmEqNatSubst (sbFund Γ⊢γ⇒Δ)
...| T.TmEqZeroSubst Γ⊢γ⇒Δ = TmEqZeroSubst (sbFund Γ⊢γ⇒Δ)
...| T.TmEqSuccSubst Δ⊢Succa∷Nat Γ⊢γ⇒Δ = TmEqSuccSubst (tmFund Δ⊢Succa∷Nat) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqNatElimSubst Δ⊢NatElim∷A[id◀c] Γ⊢γ⇒Δ = TmEqNatElimSubst (tmFund Δ⊢NatElim∷A[id◀c]) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqSubstSubst Ξ⊢a∷A Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = TmEqSubstSubst (tmFund Ξ⊢a∷A) (sbFund Δ⊢δ⇒Ξ) (sbFund Γ⊢γ⇒Δ)
...| T.TmEqUSubst Γ⊢γ⇒Δ = TmEqUSubst (sbFund Γ⊢γ⇒Δ)
-- β rules
...| T.TmEqPiBeta Γ⊢A Γ◁A⊢b∷B Γ⊢a∷A = TmEqPiBeta (tyFund Γ⊢A) (tmFund Γ◁A⊢b∷B) (tmFund Γ⊢a∷A)
...| T.TmEqNatElimZero Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] = TmEqNatElimZero (tyFund Γ◁ℕ⊢A) (tmFund Γ⊢a∷A[id◀Z]) (tmFund Γ◁ℕ◁A⊢b∷A[drop2◀SVar1])
...| T.TmEqNatElimSucc Γ◁ℕ⊢A Γ⊢a∷A[id◀Z] Γ◁ℕ◁A⊢b∷A[drop2◀SVar1] Γ⊢c∷ℕ = TmEqNatElimSucc (tyFund Γ◁ℕ⊢A) (tmFund Γ⊢a∷A[id◀Z]) (tmFund Γ◁ℕ◁A⊢b∷A[drop2◀SVar1]) (tmFund Γ⊢c∷ℕ)
-- η rules
...| T.TmEqPiEta Γ⊢f∷PiAB = TmEqPiEta (tmFund Γ⊢f∷PiAB)
...| T.TmEqNatEta Γ⊢c∷ℕ = TmEqNatEta (tmFund Γ⊢c∷ℕ)

sbEqFund eq with eq
-- Eq
...| T.SbEqSym Γ⊢γ₂≡γ₁⇒Δ = SbEqSym (sbEqFund Γ⊢γ₂≡γ₁⇒Δ)
...| T.SbEqTrans Γ⊢γ₁≡γ₂⇒Δ Γ⊢γ₂≡γ₃⇒Δ = SbEqTrans (sbEqFund Γ⊢γ₁≡γ₂⇒Δ) (sbEqFund Γ⊢γ₂≡γ₃⇒Δ)
-- congruence
...| T.SbEqExt Γ⊢γ₁≡γ₂⇒Δ Δ⊢A Γ⊢a≡b∷Aγ₁ = SbEqExt (sbEqFund Γ⊢γ₁≡γ₂⇒Δ) (tyFund Δ⊢A) (tmEqFund Γ⊢a≡b∷Aγ₁)
...| T.SbEqComp Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = SbEqComp (sbEqFund Δ⊢δ₁≡δ₂⇒Ξ) (sbEqFund Γ⊢γ₁≡γ₂⇒Δ)
...| T.SbEqConv Γ⊢γ₁≡γ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = SbEqConv (sbEqFund Γ⊢γ₁≡γ₂⇒Δ₁) (ctxEqFund ⊢Δ₁≡Δ₂)
-- Computation
...| T.SbEqCompAssoc Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = SbEqCompAssoc (sbFund Ξ⊢ξ⇒Θ) (sbFund Δ⊢δ⇒Ξ) (sbFund Γ⊢γ⇒Δ)
...| T.SbEqIdₗ Δ⊢id⇒Ξ Γ⊢γ⇒Δ = SbEqIdₗ (sbFund Δ⊢id⇒Ξ) (sbFund Γ⊢γ⇒Δ)
...| T.SbEqIdᵣ Δ⊢γ⇒Ξ Γ⊢id⇒Δ = SbEqIdᵣ (sbFund Δ⊢γ⇒Ξ) (sbFund Γ⊢id⇒Δ)
...| T.SbEqExtVar Γ⊢Var0∷A = SbEqExtVar (tmFund Γ⊢Var0∷A)
...| T.SbEqDropExt Δ⊢drop1⇒Ξ Γ⊢γ◀a⇒Δ = SbEqDropExt (sbFund Δ⊢drop1⇒Ξ) (sbFund Γ⊢γ◀a⇒Δ)
...| T.SbEqDropComp Δ⊢dropX⇒Ξ Γ⊢drop1⇒Δ = SbEqDropComp (sbFund Δ⊢dropX⇒Ξ) (sbFund Γ⊢drop1⇒Δ)
...| T.SbEqExtComp Δ⊢δ◀a⇒Ξ Γ⊢γ⇒Δ = SbEqExtComp (sbFund Δ⊢δ◀a⇒Ξ) (sbFund Γ⊢γ⇒Δ)