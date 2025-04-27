{-# OPTIONS --without-K --safe #-}

module Otus.Syntax.Typed.Base where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Θ Ξ : Context
    γ γ₁ γ₂ γ₃ δ δ₁ δ₂ δ₃ ξ : Substitution
    A B C D : Term
    f g a b c d : Term

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
        →  ⊢ Γ , A
open ⊢_

data _⊢_ where
    TyPi : Γ ⊢ A → Γ , A ⊢ B
        → Γ ⊢ Pi A B
    TyU : ⊢ Γ → Γ ⊢ U l
    TySubst : Δ ⊢ A → Γ ⊢ γ ⇒ Δ 
        → Γ ⊢ (A [ γ ]ₑ)
    TyRussel : Γ ⊢ A ∷ U l
        → Γ ⊢ A

open _⊢_

data _⊢_⇒_ where
    SbId : ⊢ Γ ≡ⱼ Δ → Γ ⊢ idₛ ⇒ Δ
    SbDropˢ : Γ ⊢ drop x ⇒ Δ → Γ ⊢ A
        → Γ , A ⊢ drop (suc x) ⇒ Δ
    SbExt : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ a ∷ (A [ γ ]ₑ)
        → Γ ⊢ γ , a ⇒ Δ , A
    SbComp : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ δ ∘ γ ⇒ Ξ

open _⊢_⇒_

data _⊢_∷_ where
    TmVar : Γ ⊢ A
        → Γ , A ⊢ Var 0 ∷ (A [ drop 1 ]ₑ)
    TmLam : Γ , A ⊢ b ∷ B
        → Γ ⊢ Lam b ∷ Pi A B
    TmPi : Γ ⊢ A ∷ U l₁ → Γ , A ⊢ B ∷ U l₂
        → Γ ⊢ Pi A B ∷ U (l₁ ⊔ l₂)
    TmApp : Γ ⊢ f ∷ Pi A B → Γ ⊢ a ∷ A
        → Γ ⊢ f ∙ a ∷ (B [ idₛ , a ]ₑ)
    TmSubst : Δ ⊢ a ∷ A → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (a [ γ ]ₑ) ∷ (A [ γ ]ₑ)
    TmU : ⊢ Γ 
        → Γ ⊢ U l ∷ U (lsuc l)
    TmTyConv : Γ ⊢ a ∷ A → Γ ⊢ A ≡ⱼ B
        → Γ ⊢ a ∷ B
open _⊢_∷_


data ⊢_≡ⱼ_ where
    CEqRefl : ⊢ Γ → ⊢ Γ ≡ⱼ Γ
    CEqSym : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Γ
    CEqTrans : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Ξ → ⊢ Γ ≡ⱼ Ξ
    CEqExt : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ B → Γ ⊢ A ≡ⱼ B
        → ⊢ Γ , A ≡ⱼ Δ , B

data _⊢_≡ⱼ_ where
--- Eq
    TyEqRefl : Γ ⊢ A
        → Γ ⊢ A ≡ⱼ A
    TyEqSym : Γ ⊢ A ≡ⱼ B
        → Γ ⊢ B ≡ⱼ A
    TyEqTrans : Γ ⊢ A ≡ⱼ B → Γ ⊢ B ≡ⱼ C
        → Γ ⊢ A ≡ⱼ C
---- Cong
    TyEqPi : Γ ⊢ A ≡ⱼ B → Γ , A ⊢ C ≡ⱼ D
        →   Γ ⊢ (Pi A C) ≡ⱼ (Pi B D)
    TyEqU : l₁ ≡ l₂
        → Γ ⊢ (U l₁) ≡ⱼ U l₂
    TyEqSubst : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ (A [ γ₁ ]ₑ) ≡ⱼ (B [ γ₂ ]ₑ)
    TyEqRussel : Γ ⊢ A ≡ⱼ B ∷ U l
        → Γ ⊢ A ≡ⱼ B
---- Subst
    TyEqPiSubst : Δ ⊢ Pi A B → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (Pi A B) [ γ ]ₑ ≡ⱼ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ)
    TyEqUSubst : Δ ⊢ U l → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ U l [ γ ]ₑ ≡ⱼ U l
    TyEqSubstSubst : Δ ⊢ (A [ δ ]ₑ) → Γ ⊢ γ ⇒ Δ
        → Γ ⊢  (A [ δ ]ₑ [ γ ]ₑ) ≡ⱼ (A [ δ ∘ γ ]ₑ)

data _⊢_≡ⱼ_⇒_ where
---- Eq
    SbEqRefl : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ γ ≡ⱼ γ ⇒ Δ
    SbEqSym : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ
    SbEqTrans : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ
        → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
---- congruence
    SbEqDrop : x ≡ y → Γ ⊢ drop x ⇒ Δ
        → Γ ⊢ drop x ≡ⱼ drop y ⇒ Δ
    SbEqExt : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ a ≡ⱼ b ∷ (A [ γ₁ ]ₑ)
        → Γ ⊢ γ₁ , a ≡ⱼ γ₂ , b  ⇒ Δ , A
    SbEqComp : Δ ⊢ δ₁ ≡ⱼ δ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ δ₁ ∘ γ₁ ≡ⱼ δ₂ ∘ γ₂ ⇒ Ξ
---- Computation
    SbEqCompAssoc : Ξ ⊢ ξ ⇒ Θ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ ξ ∘ δ ∘ γ ≡ⱼ ξ ∘ (δ ∘ γ) ⇒ Θ
    SbEqIdₗ : Δ ⊢ idₛ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ idₛ ∘ γ ≡ⱼ γ ⇒ Ξ
    SbEqIdᵣ : Δ ⊢ γ ⇒ Ξ → Γ ⊢ idₛ ⇒ Δ
        → Γ ⊢ γ ∘ idₛ ≡ⱼ γ ⇒ Ξ
    SbEqExtVar : Γ ⊢ (drop 1) , Var 0  ⇒ Δ → Γ ⊢ idₛ  ⇒ Δ
        →  Γ ⊢ (drop 1), Var 0 ≡ⱼ idₛ  ⇒ Δ
    SbEqDropExt : Δ ⊢ drop 1 ⇒ Ξ → Γ ⊢ γ , a ⇒ Δ
        → Γ ⊢ drop 1 ∘ (γ , a)≡ⱼ γ ⇒ Ξ
    SbEqDropComp : Δ ⊢ drop x ⇒ Ξ → Γ ⊢ idₛ ⇒ Δ
        → Γ ⊢ drop x ∘ drop 1 ≡ⱼ drop (suc x)  ⇒ Ξ 
    SbEqExtComp : Δ ⊢ δ , a ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (δ , a) ∘ γ ≡ⱼ(δ ∘ γ , (a [ γ ]ₑ))  ⇒ Ξ

open _⊢_≡ⱼ_⇒_

module Subst-≡ⱼ-Comp where
    infixl 2 _⟨⟩_
    
    _⟨⟩_ : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
    _⟨⟩_ = SbEqTrans
    
data _⊢_≡ⱼ_∷_ where
---- Eq
    TmEqRefl : Γ ⊢ a ∷ A
        → Γ ⊢ a ≡ⱼ a ∷ A
    TmEqSym : Γ ⊢ a ≡ⱼ b ∷ A
        → Γ ⊢ b ≡ⱼ a ∷ B
    TmEqTrans : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ b ≡ⱼ c ∷ A
        → Γ ⊢ a ≡ⱼ c ∷ A
    TmEqCong : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ A
        → Δ ⊢ a ≡ⱼ b ∷ B
---- congruence
    TmEqLam : Γ , A ⊢ a ≡ⱼ b ∷ B
        → Γ ⊢ (Lam a) ≡ⱼ (Lam b) ∷ Pi A B
    TmEqPi : Γ ⊢ A ≡ⱼ B ∷ U l₁ → Γ , A ⊢ C ≡ⱼ D ∷ U l₂
        → Γ ⊢ (Pi A B) ≡ⱼ (Pi C D) ∷ U (l₁ ⊔ l₂)
    TmEqApp : Γ ⊢ f ≡ⱼ g ∷ (Pi A B) → Γ ⊢ a ≡ⱼ b ∷ A
        → Γ ⊢ (f ∙ a) ≡ⱼ (g ∙ b) ∷ (B [ idₛ , a ]ₑ)
    TmEqU : l₁ ≡ l₂
        → Γ ⊢ (U l₁) ≡ⱼ (U l₂) ∷ U (lsuc l₁)
    TmEqSubst : Δ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ (a [ γ₁ ]ₑ) ≡ⱼ (b [ γ₂ ]ₑ) ∷ (A [ γ₁ ]ₑ)

---- Subst
    TmEqSubstId : Γ ⊢ a ∷ A
        → Γ ⊢ a [ idₛ ]ₑ ≡ⱼ a ∷ A
    TmEqSubstVarExt : Δ ⊢ Var 0 ∷ A → Γ ⊢ γ , a ⇒ Δ
        → Γ ⊢ (Var 0) [ γ , a ]ₑ ≡ⱼ a ∷ (A [ γ , a ]ₑ)
    TmEqSubstVarDrop : Δ ⊢ Var x ∷ A → Γ ⊢ drop y ⇒ Δ
        → Γ ⊢ (Var x) [ drop y ]ₑ ≡ⱼ Var (x + y) ∷ (A [ drop y ]ₑ)

---- Term Subst
    TmEqLamSubst : Δ ⊢ Lam a ∷ Pi A B → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (Lam a) [ γ ]ₑ ≡ⱼ Lam (a [ lift γ ]ₑ ) ∷ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ)
    TmEqPiSubst : Δ ⊢ Pi A B ∷ U l → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (Pi A B) [ γ ]ₑ ≡ⱼ Pi ( A [ γ ]ₑ ) ( B [ lift γ ]ₑ) ∷ U l 
    TmEqAppSubst : Δ ⊢ f ∙ a ∷ A → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ ((f ∙ a) [ γ ]ₑ) ≡ⱼ (f [ γ ]ₑ) ∙ (a [ γ ]ₑ) ∷ (A [ γ ]ₑ)
    
    TmEqSubstComp :  Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ a ∷ A
        → Γ ⊢ (a [ δ ]ₑ [ γ ]ₑ) ≡ⱼ (a [ δ ∘ γ ]ₑ) ∷ (A [ δ ∘ γ ]ₑ)
    TmEqUSubst : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (U l [ γ ]ₑ) ≡ⱼ U l ∷ U (lsuc l₁)

---- β rules
    TmEqPiBeta : Γ , A ⊢ b ∷ B → Γ ⊢ a ∷ A
        → Γ ⊢ (Lam b) ∙ a ≡ⱼ (b [ idₛ , a ]ₑ) ∷ (B [ idₛ , a ]ₑ)
---- η rules
    TmEqPiEta : Γ ⊢ f ∷ (Pi A B)
        → Γ ⊢ f ≡ⱼ (Lam ((f [ drop 1 ]ₑ) ∙ Var 0)) ∷ (B [ idₛ , a ]ₑ)

open _⊢_≡ⱼ_∷_