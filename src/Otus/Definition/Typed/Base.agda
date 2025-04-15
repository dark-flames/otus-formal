module Otus.Definition.Typed.Base where

open import Otus.Definition.Universe
open import Otus.Definition.Untyped

open import Data.Nat hiding (_⊔_)

infixl 30 _,_

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ  : Context
    γ δ : Substitution
    f a b A B : Term

data _⊢_ : Context → Term → Set
data _⊢_::_ : Context → Term → Term → Set

data ⊢_ : Context → Set where
    ε : ⊢ ε
    _,_ : ( ⊢ Γ )
        → ( Γ ⊢ A )
        → ( ⊢ Γ , A )


data _∷_∈_ : ℕ → Term → Context → Set where
    current : 0 ∷ A ∈ Γ , A
    next : x ∷ A ∈ Γ 
        → suc x ∷ A ∈ Γ , B

data _⊢_ where
    TyPi : Γ ⊢ A → Γ , A ⊢ B
        → Γ ⊢ Pi A B
    TyU : Γ ⊢ U l
    TyRussel :  Γ ⊢ A :: U l
        → Γ ⊢ A

data _⊢_⇒_ : Context → Substitution → Context → Set where
    SbDropᶻ : Γ ⊢ drop 0 ⇒ Γ
    SbDropˢ : Γ , A ⊢ drop (suc x) ⇒ Δ
        → Γ ⊢ drop x ⇒ Δ
    SbExt : Γ ⊢ γ ⇒ Δ → Δ ⊢ A → Γ ⊢ a :: (A [ γ ]ₑ)
        → Γ ⊢ γ , a ⇒ Δ , A
    SbComp : Δ ⊢ δ ⇒ Ξ → Γ ⊢ γ ⇒ Δ
        → Γ ⊢ δ ∘ γ ⇒ Δ

data _⊢_::_ where
    TmVar : x ∷ A ∈ Γ
        → Γ ⊢ Var x :: A
    TmLam : Γ , A ⊢ b :: B
        → Γ ⊢ Lam b :: Pi A B
    TmPi : Γ ⊢ A :: U l₁ → Γ , A ⊢ B :: U l₂
        → Γ ⊢ Pi A B :: U (l₁ ⊔ l₂)
    TmApp : Γ ⊢ f :: Pi A B → Γ ⊢ a :: a
        → Γ ⊢ a ∙ b :: (B [ idₛ , a ]ₑ)
    TmU : Γ ⊢ U l :: U (lsuc l)