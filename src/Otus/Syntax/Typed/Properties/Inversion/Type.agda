{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Context
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Inversion.Base
open import Otus.Syntax.Typed.Properties.Inversion.Term


private
  variable
    Γ : Context
    A B : Term

piTyInversion : Γ ⊢ Pi A B → Γ ⊢ A × Γ ◁ A ⊢ B
piTyInversion (TyPi Γ⊢A Γ◁A⊢B) = Γ⊢A , Γ◁A⊢B
piTyInversion (TyRussel Γ⊢PiAB∷T) = let 
    inv , Γ⊢T≡Ul , Γ⊢A∷Ul₁ , Γ◁A⊢B∷Ul₂ = piTmInversion Γ⊢PiAB∷T
  in TyRussel Γ⊢A∷Ul₁ , TyRussel Γ◁A⊢B∷Ul₂



   