module Otus.Syntax.Typed.Eq.Properties where

open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Eq.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ  : Context
    γ δ : Substitution
    A B C D : Term

---- Deburijn Index
db-index-coe : x ≡ y → x ∷ A ∈ Γ 
  → y ∷ A ∈ Γ 
db-index-coe refl prop = prop
---- Ctx Eq