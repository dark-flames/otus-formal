{-# OPTIONS --without-K --safe #-}

module Otus.Syntax.Typed.Presupposition.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped

open Nat

private
  variable
    u u₁ u₂ : Universe
    x y n : ℕ
    Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ ξ : Substitution
    A A₁ A₂ B C D : Type
    f g a a₁ a₂ b b₁ b₂ c c₁ c₂ d  : Term

infix 6 ⊢_ _⊢_∈ᵤ_ _⊢_≡ⱼ_∈ᵤ_ _⊢_ _⊢_∷_ _⊢_⇒_ ⊢_≡ⱼ_ _⊢_≡ⱼ_ _⊢_≡ⱼ_⇒_ _⊢_≡ⱼ_∷_

data ⊢_ : Context → Set
data _⊢_∷_ : Context → Term → Type → Set
data _⊢_⇒_ : Context → Substitution → Context → Set
data ⊢_≡ⱼ_ : Context → Context → Set 
data _⊢_≡ⱼ_⇒_ : Context → Substitution → Substitution → Context → Set
data _⊢_≡ⱼ_∷_ : Context → Term → Term → Type → Set

_⊢_∈ᵤ_ : Context → Type → Universe → Set
_⊢_∈ᵤ_ Γ A u = Γ ⊢ A ∷ Univ u

_⊢_≡ⱼ_∈ᵤ_ : Context → Type → Type → Universe → Set
_⊢_≡ⱼ_∈ᵤ_ Γ A B u = Γ ⊢ A ≡ⱼ B ∷ Univ u

record _⊢_ (Γ : Context) (A : Type) : Set where
  inductive
  constructor tyJdg
  field
    tyUniv : Universe
    Γ⊢A∷U  : Γ ⊢ A ∈ᵤ tyUniv

record _⊢_≡ⱼ_ (Γ : Context) (A B : Type) : Set where
  inductive
  constructor tyEqJdg
  field
    tyUniv  : Universe
    Γ⊢A≡B∷U : Γ ⊢ A ≡ⱼ B ∈ᵤ tyUniv

data ⊢_ where
  CEmp : ⊢ ε
  CExt : ⊢ Γ → Γ ⊢ A
      -----------------
       → ⊢ Γ ◁ A
open ⊢_

data _⊢_∷_ where
  TmVarᶻ : Γ ⊢ A
    → Γ ◁ A ⊢ Var 0 ∷ A [ drop 1 ]ₑ
  TmVarˢ : Γ ⊢ Var x ∷ A → Γ ⊢ B
    → Γ ◁ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
  TmPi : Γ ⊢ A ∷ Univ u₁ → Γ ◁ A ⊢ B ∷ Univ u₂
    → Γ ⊢ Pi A B ∷ Univ (u₁ ⊔ᵤ u₂)
  TmLam : Γ ⊢ A → Γ ◁ A ⊢ b ∷ B
    → Γ ⊢ Lam b ∷ Pi A B
  TmApp : Γ ⊢ f ∷ Pi A B → Γ ⊢ a ∷ A
    → Γ ⊢ f ∙ a ∷ B [ idₛ ◀ a ]ₑ
  TmNat : ⊢ Γ
    → Γ ⊢ Nat ∷ Univ univ₀
  TmZero : ⊢ Γ
    → Γ ⊢ Zero ∷ Nat
  TmSucc : Γ ⊢ a ∷ Nat
    → Γ ⊢ Succ a ∷ Nat
  TmNatElim : Γ ◁ Nat ⊢ A → Γ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ 
    → Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ 
    → Γ ⊢ c ∷ Nat
    -- -----------------
    → Γ ⊢ NatElim A a b c ∷ A [ idₛ ◀ c ]ₑ
  TmSubst : Δ ⊢ a ∷ A → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ γ ]ₑ ∷ A [ γ ]ₑ
  TmUniv : ⊢ Γ 
    → Γ ⊢ Univ u ∷ Univ (lsuc u)
  TmCum : Γ ⊢ A ∷ Univ u
    → Γ ⊢ A ∷ Univ (lsuc u)
  TmTyConv : Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ∷ B
open _⊢_∷_

data _⊢_⇒_ where
  SbId : ⊢ Γ → Γ ⊢ idₛ ⇒ Γ
  SbDropˢ : Γ ⊢ drop x ⇒ Δ → Γ ⊢ A
    → Γ ◁ A ⊢ drop (1 + x) ⇒ Δ
  SbExt : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ∷ (A [ γ ]ₑ)
    → Γ ⊢ γ ◀ a ⇒ Δ ◁ A
  SbComp : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ δ ∘ γ ⇒ Ξ
  SbConv : Γ ⊢ γ ⇒ Δ₁ → ⊢ Δ₁ ≡ⱼ Δ₂ 
    → Γ ⊢ γ ⇒ Δ₂
open _⊢_⇒_


data ⊢_≡ⱼ_ where
  CEqEmp : ⊢ ε ≡ⱼ ε
  CEqExt :  ⊢ Γ ≡ⱼ Δ
    → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B
    → Δ ⊢ A → Δ ⊢ B → Δ ⊢ A ≡ⱼ B
    → ⊢ Γ ◁ A ≡ⱼ Δ ◁ B
open ⊢_≡ⱼ_

data _⊢_≡ⱼ_∷_ where
---- Eq
  TmEqSym : Γ ⊢ a ≡ⱼ b ∷ A
    → Γ ⊢ b ≡ⱼ a ∷ A
  TmEqTrans : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ b ≡ⱼ c ∷ A
    → Γ ⊢ a ≡ⱼ c ∷ A
---- Congruence
  TmEqLam : Γ ⊢ A → Γ ◁ A ⊢ a ≡ⱼ b ∷ B -- todo : `Γ ⊢ A` required by context conv (tc)
    → Γ ⊢ Lam a ≡ⱼ Lam b ∷ Pi A B
  TmEqPi : Γ ⊢ A → Γ ⊢ A ≡ⱼ B ∷ Univ u₁ → Γ ◁ A ⊢ C ≡ⱼ D ∷ Univ u₂ -- todo : `Γ ⊢ A` required by context conv (tc)
    → Γ ⊢ Pi A C ≡ⱼ Pi B D ∷ Univ (u₁ ⊔ᵤ u₂)
  TmEqApp : Γ ⊢ Pi A B → Γ ⊢ f ≡ⱼ g ∷ Pi A B → Γ ⊢ a ≡ⱼ b ∷ A
    → Γ ⊢ f ∙ a ≡ⱼ g ∙ b ∷ B [ idₛ ◀ a ]ₑ
  TmEqSucc : Γ ⊢ a ≡ⱼ b ∷ Nat
    → Γ ⊢ Succ a ≡ⱼ Succ b ∷ Nat
  TmEqNatElim : Γ ◁ Nat ⊢ A₁ -- todo : `Γ ⊢ A` required by context conv (tc)
    → Γ ◁ Nat ⊢ A₁ ≡ⱼ A₂ 
    → Γ ⊢ a₁ ≡ⱼ a₂ ∷ A₁ [ idₛ ◀ Zero ]ₑ 
    → Γ ◁ Nat ◁ A₁ ⊢ b₁ ≡ⱼ b₂ ∷ A₁ [ drop 2 ◀ Succ (Var 1) ]ₑ 
    → Γ ⊢ c₁ ≡ⱼ c₂ ∷ Nat
    -- -----------------
    → Γ ⊢ NatElim A₁ a₁ b₁ c₁ ≡ⱼ NatElim A₂ a₂ b₂ c₂ ∷ A₁ [ idₛ ◀ c₁ ]ₑ
  TmEqSubst : Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ a [ γ₁ ]ₑ ≡ⱼ b [ γ₂ ]ₑ ∷ A [ γ₁ ]ₑ
  TmEqCum : Γ ⊢ A ≡ⱼ B ∷ Univ u
    → Γ ⊢ A ≡ⱼ B ∷ Univ (lsuc u)
  TmEqConv : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ A ≡ⱼ B
    → Γ ⊢ a ≡ⱼ b ∷ B
---- Subst Computation
  TmEqSubstId : Γ ⊢ a ∷ A
    → Γ ⊢ a [ idₛ ]ₑ ≡ⱼ a ∷ A
  TmEqSubstVarExt : Δ ⊢ Var 0 ∷ A → Γ ⊢ γ ◀ a ⇒ Δ
    → Γ ⊢ Var 0 [ γ ◀ a ]ₑ ≡ⱼ a ∷ A [ γ ◀ a ]ₑ
  TmEqSubstVarDrop : Δ ⊢ Var x ∷ A → Γ ⊢ drop y ⇒ Δ
    → Γ ⊢ Var x [ drop y ]ₑ ≡ⱼ Var (y + x) ∷ (A [ drop y ]ₑ)
  TmEqLamSubst : Δ ⊢ Lam a ∷ Pi A B → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Lam a [ γ ]ₑ ≡ⱼ Lam (a [ lift γ ]ₑ) ∷ Pi A B [ γ ]ₑ
  TmEqPiSubst : Δ ⊢ Pi A B ∷ Univ u → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Pi A B [ γ ]ₑ ≡ⱼ Pi (A [ γ ]ₑ) (B [ lift γ ]ₑ) ∷ Univ u 
  TmEqAppSubst : Δ ⊢ f ∙ a ∷ A → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ f ∙ a [ γ ]ₑ ≡ⱼ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ (A [ γ ]ₑ)
  TmEqNatSubst : Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Nat [ γ ]ₑ ≡ⱼ Nat ∷ Univ univ₀
  TmEqZeroSubst : Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Zero [ γ ]ₑ ≡ⱼ Zero ∷ Nat
  TmEqSuccSubst : Δ ⊢ Succ a ∷ Nat → Γ ⊢ γ ⇒ Δ 
    → Γ ⊢ Succ a [ γ ]ₑ ≡ⱼ Succ (a [ γ ]ₑ) ∷ Nat
  TmEqNatElimSubst : Δ ⊢ NatElim A a b c ∷ A [ idₛ ◀ c ]ₑ → Γ ⊢ γ ⇒ Δ
    -- -----------------
    → Γ ⊢ NatElim A a b c [ γ ]ₑ ≡ⱼ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ idₛ ◀ c ]ₑ [ γ ]ₑ
  TmEqSubstSubst :  Ξ ⊢ a ∷ A → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ a [ δ ]ₑ [ γ ]ₑ ≡ⱼ a [ δ ∘ γ ]ₑ ∷ A [  δ ∘ γ ]ₑ
  TmEqUSubst : Γ ⊢ γ ⇒ Δ
    → Γ ⊢ Univ u [ γ ]ₑ ≡ⱼ Univ u ∷ Univ (lsuc u)
---- β rules
  TmEqPiBeta : Γ ⊢ A → Γ ◁ A ⊢ b ∷ B → Γ ⊢ a ∷ A
    → Γ ⊢ (Lam b) ∙ a ≡ⱼ b [ idₛ ◀ a ]ₑ ∷ B [ idₛ ◀ a ]ₑ
  TmEqNatElimZero : Γ ◁ Nat ⊢ A → Γ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ 
    → Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ 
    -- -----------------
    → Γ ⊢ NatElim A a b Zero ≡ⱼ a ∷ A [ idₛ ◀ Zero ]ₑ
  TmEqNatElimSucc : Γ ◁ Nat ⊢ A → Γ ⊢ a ∷ A [ idₛ ◀ Zero ]ₑ 
    → Γ ◁ Nat ◁ A ⊢ b ∷ A [ drop 2 ◀ Succ (Var 1) ]ₑ 
    → Γ ⊢ c ∷ Nat
    -- -----------------
    → Γ ⊢ NatElim A a b (Succ c) ≡ⱼ b [ idₛ ◀ c ◀ NatElim A a b c ]ₑ ∷ A [ idₛ ◀ (Succ c) ]ₑ
---- η rules
  TmEqPiEta : Γ ⊢ f ∷ Pi A B
    → Γ ⊢ f ≡ⱼ Lam ((f [ drop 1 ]ₑ) ∙ Var 0) ∷ Pi A B
  TmEqNatEta : Γ ⊢ c ∷ Nat
    → Γ ⊢ NatElim Nat Zero (Succ (Var 0)) c ≡ⱼ c ∷ Nat

open _⊢_≡ⱼ_∷_

data _⊢_≡ⱼ_⇒_ where
---- Eq
  SbEqSym : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ
  SbEqTrans : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ
    → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
---- congruence
  SbEqExt : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ≡ⱼ b ∷ A [ γ₁ ]ₑ 
    → Γ ⊢ γ₁ ◀ a ≡ⱼ γ₂ ◀ b  ⇒ Δ ◁ A
  SbEqComp : Δ ⊢ δ₁ ≡ⱼ δ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
    → Γ ⊢ δ₁ ∘ γ₁ ≡ⱼ δ₂ ∘ γ₂ ⇒ Ξ
  SbEqConv : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ₁ → ⊢ Δ₁ ≡ⱼ Δ₂
    → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ₂
---- Computation
  SbEqCompAssoc : Ξ ⊢ ξ ⇒ Θ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ ξ ∘ δ ∘ γ ≡ⱼ ξ ∘ (δ ∘ γ) ⇒ Θ
  SbEqIdₗ : Δ ⊢ idₛ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ idₛ ∘ γ ≡ⱼ γ ⇒ Ξ
  SbEqIdᵣ : Δ ⊢ γ ⇒ Ξ → Γ ⊢ idₛ ⇒ Δ
    → Γ ⊢ γ ∘ idₛ ≡ⱼ γ ⇒ Ξ
  SbEqExtVar : Γ ⊢ Var 0 ∷ A
    →  Γ ⊢ drop 1 ◀ Var 0 ≡ⱼ idₛ  ⇒ Γ
  SbEqDropExt : Δ ⊢ drop 1 ⇒ Ξ → Γ ⊢ γ ◀ a ⇒ Δ
    → Γ ⊢ drop 1 ∘ γ ◀ a ≡ⱼ γ ⇒ Ξ
  SbEqDropComp : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ drop 1 ⇒ Δ
    → Γ ⊢ drop x ∘ drop 1 ≡ⱼ drop (1 + x)  ⇒ Ξ 
  SbEqExtComp : Δ ⊢ δ ◀ a ⇒ Ξ → Γ ⊢ γ ⇒ Δ
    → Γ ⊢ δ ◀ a ∘ γ ≡ⱼ(δ ∘ γ) ◀ a [ γ ]ₑ  ⇒ Ξ
open _⊢_≡ⱼ_⇒_