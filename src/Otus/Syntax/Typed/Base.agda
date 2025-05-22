{-# OPTIONS --without-K --safe #-}

module Otus.Syntax.Typed.Base where

open import Otus.Syntax.Untyped

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    l l₁ l₂ : ULevel
    x y n : ℕ
    Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ ξ : Substitution
    A A₁ A₂ B C D : Term
    f g a a₁ a₂ b b₁ b₂ c c₁ c₂ d  : Term

infix 6 ⊢_ _⊢_ _⊢_∷_ _⊢_⇒_ ⊢_≡ⱼ_ _⊢_≡ⱼ_ _⊢_≡ⱼ_⇒_ _⊢_≡ⱼ_∷_

data ⊢_ : Context → Set
data _⊢_ : Context → Term → Set
data _⊢_∷_ : Context → Term → Term → Set
data _⊢_⇒_ : Context → Substitution → Context → Set
data ⊢_≡ⱼ_ : Context → Context → Set 
data _⊢_≡ⱼ_ : Context → Term → Term → Set
data _⊢_≡ⱼ_⇒_ : Context → Substitution → Substitution → Context → Set
data _⊢_≡ⱼ_∷_ : Context → Term → Term → Term → Set

data ⊢_ where
    CEmp : ⊢ ε
    CExt : ⊢ Γ → Γ ⊢ A
        →  ⊢ Γ ◁ A
open ⊢_

data _⊢_ where
    TyPi : Γ ⊢ A → Γ ◁ A ⊢ B
        → Γ ⊢ Pi A B
    TyNat : ⊢ Γ → Γ ⊢ Nat
    TyUniv : ⊢ Γ → Γ ⊢ Univ l
    TySubst : Δ ⊢ A → Γ ⊢ γ ⇒ Δ 
        → Γ ⊢ (A [ γ ]ₑ)
    TyRussel : Γ ⊢ A ∷ Univ l
        → Γ ⊢ A

open _⊢_

data _⊢_∷_ where
    TmVarᶻ : Γ ⊢ A
        → Γ ◁ A ⊢ Var 0 ∷ A [ drop 1 ]ₑ
    TmVarˢ : Γ ⊢ Var x ∷ A → Γ ⊢ B
        → Γ ◁ B ⊢ Var (suc x) ∷ A [ drop 1 ]ₑ
    TmPi : Γ ⊢ A ∷ Univ l₁ → Γ ◁ A ⊢ B ∷ Univ l₂
        → Γ ⊢ Pi A B ∷ Univ (l₁ ⊔ l₂)
    TmLam : Γ ⊢ A → Γ ◁ A ⊢ b ∷ B
        → Γ ⊢ Lam b ∷ Pi A B
    TmApp : Γ ⊢ f ∷ Pi A B → Γ ⊢ a ∷ A
        → Γ ⊢ f ∙ a ∷ B [ idₛ ◀ a ]ₑ
    TmNat : ⊢ Γ
        → Γ ⊢ Nat ∷ Univ lBottom
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
        → Γ ⊢ Univ l ∷ Univ (lsuc l)
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
    CEqRefl : ⊢ Γ → ⊢ Γ ≡ⱼ Γ
    CEqExt : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B
        → ⊢ Γ ◁ A ≡ⱼ Δ ◁ B

data _⊢_≡ⱼ_ where
--- Eq
    TyEqRefl : Γ ⊢ A
        → Γ ⊢ A ≡ⱼ A
    TyEqSym : Γ ⊢ A ≡ⱼ B
        → Γ ⊢ B ≡ⱼ A
    TyEqTrans : Γ ⊢ A ≡ⱼ B → Γ ⊢ B ≡ⱼ C
        → Γ ⊢ A ≡ⱼ C
---- Cong
    TyEqPi : Γ ⊢ A → Γ ⊢ A ≡ⱼ B → Γ ◁ A ⊢ C ≡ⱼ D -- todo : `Γ ⊢ A` required by context conv (tc)
        → Γ ⊢ Pi A C ≡ⱼ Pi B D
    TyEqSubst : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ A [ γ₁ ]ₑ ≡ⱼ B [ γ₂ ]ₑ
    TyEqRussel : Γ ⊢ A ≡ⱼ B ∷ Univ l
        → Γ ⊢ A ≡ⱼ B
---- Subst Computation
    TyEqPiSubst : Δ ⊢ Pi A B → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Pi A B [ γ ]ₑ ≡ⱼ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ) -- (γ ∘ drop 1) ◀ Var 0
    TyEqUSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Univ l [ γ ]ₑ ≡ⱼ Univ l
    TyEqNatSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Nat [ γ ]ₑ ≡ⱼ Nat
    TyEqSubstSubst : Ξ ⊢ A → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢  A [ δ ]ₑ [ γ ]ₑ ≡ⱼ A [ δ ∘ γ ]ₑ
    TyEqSubstId : Γ ⊢ A
        → Γ ⊢ A [ idₛ ]ₑ ≡ⱼ A

data _⊢_≡ⱼ_∷_ where
---- Eq
    TmEqRefl : Γ ⊢ a ∷ A
        → Γ ⊢ a ≡ⱼ a ∷ A
    TmEqSym : Γ ⊢ a ≡ⱼ b ∷ A
        → Γ ⊢ b ≡ⱼ a ∷ A
    TmEqTrans : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ b ≡ⱼ c ∷ A
        → Γ ⊢ a ≡ⱼ c ∷ A
---- Congruence
    TmEqLam : Γ ⊢ A → Γ ◁ A ⊢ a ≡ⱼ b ∷ B -- todo : `Γ ⊢ A` required by context conv (tc)
        → Γ ⊢ Lam a ≡ⱼ Lam b ∷ Pi A B
    TmEqPi : Γ ⊢ A → Γ ⊢ A ≡ⱼ B ∷ Univ l₁ → Γ ◁ A ⊢ C ≡ⱼ D ∷ Univ l₂ -- todo : `Γ ⊢ A` required by context conv (tc)
        → Γ ⊢ Pi A C ≡ⱼ Pi B D ∷ Univ (l₁ ⊔ l₂)
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
    TmEqPiSubst : Δ ⊢ Pi A B ∷ Univ l → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Pi A B [ γ ]ₑ ≡ⱼ Pi (A [ γ ]ₑ) (B [ lift γ ]ₑ) ∷ Univ l 
    TmEqAppSubst : Δ ⊢ f ∙ a ∷ A → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ f ∙ a [ γ ]ₑ ≡ⱼ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ (A [ γ ]ₑ)
    TmEqNatSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Nat [ γ ]ₑ ≡ⱼ Nat ∷ Univ lBottom
    TmEqZeroSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Zero [ γ ]ₑ ≡ⱼ Zero ∷ Nat
    TmEqSuccSubst : Δ ⊢ Succ a ∷ Nat → Γ ⊢ γ ⇒ Δ 
        → Γ ⊢ Succ a [ γ ]ₑ ≡ⱼ Succ (a [ γ ]ₑ) ∷ Nat
    TmEqNatElimSubst : Δ ⊢ NatElim A a b c ∷ A [ idₛ ◀ c ]ₑ → Γ ⊢ γ ⇒ Δ
        -- -----------------
        → Γ ⊢ NatElim A a b c [ γ ]ₑ ≡ⱼ NatElim (A [ lift γ ]ₑ) (a [ γ ]ₑ) (b [ lift (lift γ) ]ₑ) (c [ γ ]ₑ) ∷ A [ idₛ ◀ c ]ₑ [ γ ]ₑ
    TmEqSubstSubst :  Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ a ∷ A
        → Γ ⊢ a [ δ ]ₑ [ γ ]ₑ ≡ⱼ a [ δ ∘ γ ]ₑ ∷ A [ δ ]ₑ [ γ ]ₑ
    TmEqUSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ Univ l [ γ ]ₑ ≡ⱼ Univ l ∷ Univ (lsuc l)
---- β rules
    TmEqPiBeta : Γ ⊢ A → Γ ◁ A ⊢ b ∷ B → Γ ⊢ a ∷ A
        → Γ ⊢ (Lam b) ∙ a ≡ⱼ b [ idₛ ◀ a ]ₑ ∷ B [ idₛ ◀ a ]ₑ
---- η rules
    TmEqPiEta : Γ ⊢ f ∷ Pi A B
        → Γ ⊢ f ≡ⱼ Lam ((f [ drop 1 ]ₑ) ∙ Var 0) ∷ Pi A B

open _⊢_≡ⱼ_∷_

data _⊢_≡ⱼ_⇒_ where
---- Eq
    SbEqRefl : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ γ ≡ⱼ γ ⇒ Δ
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