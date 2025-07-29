{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Univ where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base

open PropositionalEq
open Nat

private
  variable
    u₁ u₂ : Universe
    Γ : Context
    A B : Type

tyUnivConv : Γ ⊢ A ∈ᵤ u₁ → u₁ ≡ u₂ → Γ ⊢ A ∈ᵤ u₂
tyUnivConv Γ⊢A∈ᵤu₁ refl = Γ⊢A∈ᵤu₁

tyUnivConv' : Γ ⊢ A ∈ᵤ u₁ → u₂ ≡ u₁ → Γ ⊢ A ∈ᵤ u₂
tyUnivConv' Γ⊢A∈ᵤu₁ refl = Γ⊢A∈ᵤu₁

tyEqUnivConv : Γ ⊢ A ≡ⱼ B ∈ᵤ u₁ → u₁ ≡ u₂ → Γ ⊢ A ≡ⱼ B ∈ᵤ u₂
tyEqUnivConv Γ⊢A≡B∈ᵤu₁ refl = Γ⊢A≡B∈ᵤu₁

tyEqUnivConv' : Γ ⊢ A ≡ⱼ B ∈ᵤ u₁ → u₂ ≡ u₁ → Γ ⊢ A ≡ⱼ B ∈ᵤ u₂
tyEqUnivConv' Γ⊢A≡B∈ᵤu₁ refl = Γ⊢A≡B∈ᵤu₁

liftTyUniv : ∀ {u} → (n : ℕ) → Γ ⊢ A ∈ᵤ u → Γ ⊢ A ∈ᵤ liftUniv n u
liftTyUniv zero Γ⊢A∈ᵤu = Γ⊢A∈ᵤu
liftTyUniv (suc n) Γ⊢A∈ᵤu = TmCum (liftTyUniv n Γ⊢A∈ᵤu)

liftTyEqUniv : ∀ {u} → (n : ℕ) → Γ ⊢ A ≡ⱼ B ∈ᵤ u → Γ ⊢ A ≡ⱼ B ∈ᵤ liftUniv n u
liftTyEqUniv zero Γ⊢A≡B∈ᵤu = Γ⊢A≡B∈ᵤu
liftTyEqUniv (suc n) Γ⊢A≡B∈ᵤu = TmEqCum (liftTyEqUniv n Γ⊢A≡B∈ᵤu)

liftTy : ∀ {u₁ u₂} → Γ ⊢ A ∈ᵤ u₁ → u₁ ⊆ u₂ → Γ ⊢ A ∈ᵤ u₂
liftTy {_} {_} {u₁} {u₂} Γ⊢A∈ᵤu₁ u₁⊆u₂ = let
    gap = Universe.level u₂ ∸ Universe.level u₁
    Γ⊢A∈ᵤu₁+g = liftTyUniv gap Γ⊢A∈ᵤu₁
    u₁+g≡u₂ = cong univ (m∸n+n≡m u₁⊆u₂)
  in tyUnivConv Γ⊢A∈ᵤu₁+g u₁+g≡u₂

liftTyEq : ∀ {u₁ u₂} → Γ ⊢ A ≡ⱼ B ∈ᵤ u₁ → u₁ ⊆ u₂ → Γ ⊢ A ≡ⱼ B ∈ᵤ u₂
liftTyEq {_} {_} {_} {u₁} {u₂} Γ⊢A≡B∈ᵤu₁ u₁⊆u₂ = let
    gap = Universe.level u₂ ∸ Universe.level u₁
    Γ⊢A≡B∈ᵤu₁+g = liftTyEqUniv gap Γ⊢A≡B∈ᵤu₁
    u₁+g≡u₂ = cong univ (m∸n+n≡m u₁⊆u₂)
  in tyEqUnivConv Γ⊢A≡B∈ᵤu₁+g u₁+g≡u₂