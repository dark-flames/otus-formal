{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Utils.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Relation

open PropositionalEq

private
  variable
    u u₁ u₂ : Universe
    x : ℕ
    Γ Δ Ξ Θ : Context
    γ γ₁ γ₂ δ ξ : Substitution
    A B C D : Type


tyEqUSubst : Γ ⊢ γ ⇒ Δ 
  → Γ ⊢ Univ u [ γ ]ₑ ≡ⱼ Univ u
tyEqUSubst {_} {_} {_} {u} Γ⊢γ⇒Δ = tyEqJdg (lsuc u) (TmEqUSubst Γ⊢γ⇒Δ)


tyPi : Γ ⊢ A → Γ ◁ A ⊢ B
  → Γ ⊢ Pi A B
tyPi (tyJdg u₁ Γ⊢A∈u₁) (tyJdg u₂ Γ◁A⊢B∈u₂) = 
    tyJdg (u₁ ⊔ᵤ u₂) (TmPi Γ⊢A∈u₁ Γ◁A⊢B∈u₂)

tyNat : ⊢ Γ → Γ ⊢ Nat
tyNat ⊢Γ = tyJdg univ₀ (TmNat ⊢Γ)

tyUniv : ⊢ Γ → Γ ⊢ Univ u
tyUniv {_} {u} ⊢Γ = tyJdg (lsuc u) (TmUniv ⊢Γ)

tySubst : Δ ⊢ A → Γ ⊢ γ ⇒ Δ → Γ ⊢ A [ γ ]ₑ
tySubst (tyJdg u Δ⊢A∈u) Γ⊢γ⇒Δ = let
    Γ⊢A[γ]∈u[γ] = TmSubst Δ⊢A∈u Γ⊢γ⇒Δ
    Γ⊢A[γ]∈u = TmTyConv Γ⊢A[γ]∈u[γ] (tyEqUSubst Γ⊢γ⇒Δ)
  in tyJdg u Γ⊢A[γ]∈u

tyRussel : Γ ⊢ A ∷ Univ u → Γ ⊢ A
tyRussel {_} {_} {u} = tyJdg u

tyEqPi :  Γ ⊢ A → Γ ⊢ A ≡ⱼ B → Γ ◁ A ⊢ C ≡ⱼ D -- todo : `Γ ⊢ A` required by context conv (tc)
    → Γ ⊢ Pi A C ≡ⱼ Pi B D
tyEqPi  Γ⊢A (tyEqJdg u₁ Γ⊢A≡B∈u₁) (tyEqJdg u₂ Γ◁A⊢C≡D∈u₂) = 
    tyEqJdg (u₁ ⊔ᵤ u₂) (TmEqPi Γ⊢A Γ⊢A≡B∈u₁ Γ◁A⊢C≡D∈u₂)

tyEqPi₁ : Γ ⊢ A → Γ ⊢ A ≡ⱼ B → Γ ◁ A ⊢ C
    → Γ ⊢ Pi A C ≡ⱼ Pi B C
tyEqPi₁ Γ⊢A Γ⊢A≡B Γ◁A⊢C = tyEqPi Γ⊢A Γ⊢A≡B (tyEqRefl Γ◁A⊢C)

tyEqPi₂ : Γ ⊢ A → Γ ◁ A ⊢ C ≡ⱼ D
    → Γ ⊢ Pi A C ≡ⱼ Pi A D
tyEqPi₂ Γ⊢A Γ◁A⊢C≡D = tyEqPi Γ⊢A (tyEqRefl Γ⊢A) Γ◁A⊢C≡D

tyEqSubst : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ₁ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ B [ γ₂ ]ₑ
tyEqSubst (tyEqJdg u Δ⊢A≡B∈u) Γ⊢γ₁⇒Δ Γ⊢γ₁≡γ₂⇒Δ = let
    Γ⊢A[γ₁]≡B[γ₂]∈u[γ₁] = TmEqSubst Δ⊢A≡B∈u Γ⊢γ₁≡γ₂⇒Δ
    Γ⊢A[γ₁]≡B[γ₂]∈u = TmEqConv Γ⊢A[γ₁]≡B[γ₂]∈u[γ₁] (tyEqUSubst Γ⊢γ₁⇒Δ)
  in tyEqJdg u Γ⊢A[γ₁]≡B[γ₂]∈u

tyEqSubst₁ : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ A [ γ ]ₑ ≡ⱼ B [ γ ]ₑ
tyEqSubst₁ Δ⊢A≡B Γ⊢γ⇒Δ = tyEqSubst Δ⊢A≡B Γ⊢γ⇒Δ (sbEqRefl Γ⊢γ⇒Δ)

tyEqSubst₂ : Δ ⊢ A → Γ ⊢ γ₁ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ A [ γ₂ ]ₑ
tyEqSubst₂ Δ⊢A Γ⊢γ₁⇒Δ Γ⊢γ₁≡γ₂⇒Δ = tyEqSubst (tyEqRefl Δ⊢A) Γ⊢γ₁⇒Δ Γ⊢γ₁≡γ₂⇒Δ

tyEqRussel : Γ ⊢ A ≡ⱼ B ∷ Univ u
    → Γ ⊢ A ≡ⱼ B
tyEqRussel {_} {_} {_} {u} = tyEqJdg u

tyEqPiSubst : Δ ⊢ Pi A B → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Pi A B [ γ ]ₑ ≡ⱼ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ)
tyEqPiSubst (tyJdg u Δ⊢PiAB∷U) Γ⊢γ⇒Δ = tyEqJdg u (TmEqPiSubst Δ⊢PiAB∷U Γ⊢γ⇒Δ)

tyEqNatSubst : Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Nat [ γ ]ₑ ≡ⱼ Nat
tyEqNatSubst Γ⊢γ⇒Δ = tyEqJdg univ₀ (TmEqNatSubst Γ⊢γ⇒Δ)

tyEqSubstSubst : Ξ ⊢ A → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ 
    → Γ ⊢  A [ δ ]ₑ [ γ ]ₑ ≡ⱼ A [ δ ∘ γ ]ₑ
tyEqSubstSubst (tyJdg u Ξ⊢A∈u) Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let
    Γ⊢A[δ][γ]≡A[δ∘γ]∈u[δ∘γ] = TmEqSubstSubst Ξ⊢A∈u Δ⊢δ⇒Ξ Γ⊢γ⇒Δ  
    Γ⊢δ∘γ⇒Ξ = SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ
    Γ⊢A[δ][γ]≡A[δ∘γ]∈u = TmEqConv Γ⊢A[δ][γ]≡A[δ∘γ]∈u[δ∘γ] (tyEqUSubst Γ⊢δ∘γ⇒Ξ)
  in tyEqJdg u Γ⊢A[δ][γ]≡A[δ∘γ]∈u

tyEqSubstId : Γ ⊢ A
    → Γ ⊢ A [ idₛ ]ₑ ≡ⱼ A
tyEqSubstId (tyJdg u Γ⊢A∈u) = tyEqJdg u (TmEqSubstId Γ⊢A∈u)

tyEq3Sb : Θ ⊢ A → Ξ ⊢ ξ ⇒ Θ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ A [ ξ ]ₑ [ δ ]ₑ [ γ ]ₑ ≡ⱼ A [ ξ ∘ δ ∘ γ ]ₑ
tyEq3Sb Θ⊢A Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let
    Δ⊢A[ξ][δ]≡A[ξ∘δ] = tyEqSubstSubst Θ⊢A Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ
    Δ⊢ξ∘δ⇒Θ = SbComp Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ
    Γ⊢A[ξ][δ][γ]≡A[ξ∘δ][γ] = tyEqSubst₁ Δ⊢A[ξ][δ]≡A[ξ∘δ] Γ⊢γ⇒Δ
    Γ⊢A[ξ∘δ][γ]≡A[ξ∘δ∘γ] = tyEqSubstSubst Θ⊢A Δ⊢ξ∘δ⇒Θ Γ⊢γ⇒Δ
  in tyEqTrans Γ⊢A[ξ][δ][γ]≡A[ξ∘δ][γ] Γ⊢A[ξ∘δ][γ]≡A[ξ∘δ∘γ]