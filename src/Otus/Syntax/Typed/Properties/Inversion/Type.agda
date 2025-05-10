{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Type where

open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Term

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id; _∘_)

private
  variable
    l l₁ l₂ : ULevel
    Γ Δ  : Context
    γ γ₁ γ₂ : Substitution
    A B : Term

piTyInversion : Γ ⊢ Pi A B → Γ ⊢ A × Γ , A ⊢ B
piTyInversion (TyPi Γ⊢A Γ,A⊢B) = pair Γ⊢A Γ,A⊢B
piTyInversion (TyRussel Γ⊢PiAB∷T) = let 
    pair inv (pair Γ⊢T≡Ul (pair Γ⊢A∷Ul₁ Γ,A⊢B∷Ul₂)) = piTmInversion Γ⊢PiAB∷T
  in pair (TyRussel Γ⊢A∷Ul₁) (TyRussel Γ,A⊢B∷Ul₂)



   