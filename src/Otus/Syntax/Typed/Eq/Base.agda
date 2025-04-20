module Otus.Syntax.Typed.Eq.Base where

open import Otus.Syntax.Typed.Base
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


data _⊢_≡ⱼ_ : Context → Term → Term → Set
data _⊢_≡ⱼ_∷_ : Context → Term → Term → Term → Set
data _⊢_≡ⱼ_⇒_ : Context → Substitution → Substitution → Context → Set


data ⊢_≡ⱼ_ :  Context → Context → Set where
    CEqRefl : ⊢ Γ
        → ⊢ Γ ≡ⱼ Γ
    CEqSym : ⊢ Γ₁ ≡ⱼ Γ₂
    CEqTrans : ⊢ Γ₁ ≡ⱼ Γ₂ → ⊢ Γ₂ ≡ⱼ Γ₃
        → ⊢ Γ₁ ≡ⱼ Γ₃
    CEqEmpty : ⊢ ε ≡ⱼ ε
    CEqExt : Γ ⊢ A ≡ⱼ B 
        → ⊢ (Γ , A) ≡ⱼ (Γ , B)

data _⊢_≡ⱼ_ where
-- Eq
    TyEqRefl : Γ ⊢ A
        → Γ ⊢ A ≡ⱼ A
    TyEqSym : Γ ⊢ A ≡ⱼ B
        → Γ ⊢ B ≡ⱼ A
    TyEqTrans : Γ ⊢ A ≡ⱼ B → Γ ⊢ B ≡ⱼ c
        → Γ ⊢ A ≡ⱼ C
    TyEqCong : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B
        → Δ ⊢ A ≡ⱼ B
--- Cong
    TyEqPi : Γ ⊢ A ≡ⱼ B → Γ , A ⊢ C ≡ⱼ D
        →   Γ ⊢ (Pi A B) ≡ⱼ (Pi C D)
    TyEqU : l₁ ≡ l₂
        → Γ ⊢ (U l₁) ≡ⱼ U l₂
    TyEqSubst : Δ ⊢ A ≡ⱼ B → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Δ ⊢ (A [ γ₁ ]ₑ) ≡ⱼ (B [ γ₂ ]ₑ)
    TyEqRussel : Γ ⊢ A ≡ⱼ B ∷ U l
        → Γ ⊢ A ≡ⱼ B

data _⊢_≡ⱼ_⇒_ where
---- Eq
    SbEqRefl : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ γ ≡ⱼ γ ⇒ Δ
    SbEqSym : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ γ₂ ≡ⱼ γ₁ ⇒ Δ
    SbEqTrans : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₂ ≡ⱼ γ₃ ⇒ Δ
        → Γ ⊢ γ₁ ≡ⱼ γ₃ ⇒ Δ
    SbEqCong : ⊢ Γ₁ ≡ⱼ Γ₂ → ⊢ Δ₁ ≡ⱼ Δ₂ → Γ₁ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ₁
        → Γ₂ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ₂
---- congruence
    SbEqDrop : x ≡ y → Γ ⊢ drop x ⇒ Δ
        → Γ ⊢ drop x ≡ⱼ drop y ⇒ Δ
    SbEqExt : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ a ≡ⱼ b ∷ (A [ γ₁ ]ₑ)
        → Γ ⊢ γ₁ , a ≡ⱼ γ₂ , b  ⇒ Δ , A
    SbEqComp : Δ ⊢ δ₁ ≡ⱼ δ₂ ⇒ Ξ → Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ
        → Γ ⊢ δ₁ ∘ γ₁ ≡ⱼ δ₂ ∘ γ₂ ⇒ Ξ
---- Computation
    SbEqCompAssoc : Ξ ⊢ ξ ⇒ Θ → Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (ξ ∘ δ) ∘ γ ≡ⱼ (ξ ∘ δ) ∘ γ ⇒ Θ
    SbEqIdₗ : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ drop 0 ∘ γ ≡ⱼ γ ⇒ Θ
    SbEqIdᵣ : Γ ⊢ γ ⇒ Δ
        → Γ ⊢ γ ∘ drop 0 ≡ⱼ γ ⇒ Θ
    SbEqExtVar : Γ ⊢ (drop 1) , Var 0  ⇒ Δ → Γ ⊢ idₛ  ⇒ Δ
        →  Γ ⊢ (drop 1), Var 0 ≡ⱼ idₛ  ⇒ Δ
    SbEqDropExt : Δ ⊢ drop 1 ⇒ Ξ → Γ ⊢ γ , a ⇒ Δ
        → Γ ⊢ drop 1 ∘ (γ , a)≡ⱼ γ ⇒ Ξ
    SbEqDropComp : Γ ⊢ drop (suc x) ⇒ Δ 
        → Γ ⊢ drop (suc x) ≡ⱼ drop x ∘ drop 1 ⇒ Δ 
    SbEqExtComp : Δ ⊢ δ , a ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ (δ , a) ∘ γ ≡ⱼ(δ ∘ γ , (a [ γ ]ₑ))  ⇒ Ξ

    
data _⊢_≡ⱼ_∷_ where
---- Eq
    TmEqRefl : Γ ⊢ a ∷ A
        → Γ ⊢ a ≡ⱼ a ∷ A
    TmEqSym : Γ ⊢ a ≡ⱼ b ∷ A
        → Γ ⊢ b ≡ⱼ a ∷ B
    TmEqTrans : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ b ≡ⱼ c ∷ A
        → Γ ⊢ a ≡ⱼ c ∷ A
    TmEqCong : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ A
        → Δ ⊢ a ≡ⱼ b ∷ B
---- congruence
    TmEqVar : x ≡ y → x ∷ A ∈ Γ
        → Γ ⊢ (Var x) ≡ⱼ(Var y) ∷ A
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
    TmEqSubstComp :  Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ → Ξ ⊢ a ∷ A
        → Γ ⊢ a [ δ ]ₑ [ γ ]ₑ ≡ⱼ a [ δ ∘ γ ]ₑ ∷ (A [ δ ∘ γ ]ₑ)
    
---- β rules
    TmEqPiBeta : Γ , A ⊢ b ∷ B → Γ ⊢ a ∷ A
        → Γ ⊢ (Lam b) ∙ a ≡ⱼ (b [ idₛ , a ]ₑ) ∷ (B [ idₛ , a ]ₑ)
---- η rules
    TmEqPiEta : Γ ⊢ f ∷ (Pi A B)
        → Γ ⊢ f ≡ⱼ (Lam ((f [ drop 1 ]ₑ) ∙ Var 0)) ∷ (B [ idₛ , a ]ₑ)
    





