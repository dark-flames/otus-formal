{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Heter.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presupposition
open import Otus.Syntax.Typed.Properties.Utils
open import Otus.Syntax.Typed.Properties.Context


private
  variable
    Γ : Context
    A B a b : Term


-- Heterogeneous term equality
infix 4 _⊢_∷_≡ⱼ_∷_
data _⊢_∷_≡ⱼ_∷_ : Context → Term → Term → Term → Term → Set where
    HTmEqₗ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A ≡ⱼ b ∷ B
    HTmEqᵣ : Γ ⊢ A ≡ⱼ B → Γ ⊢ a ≡ⱼ b ∷ B → Γ ⊢ a ∷ A ≡ⱼ b ∷ B