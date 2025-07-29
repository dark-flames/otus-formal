{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Universe.Base where

open import Otus.Utils

open Nat

record Universe : Set where
  inductive
  constructor univ
  field
    level : ℕ

infixl 4 _⊆_
_⊆_ : Universe → Universe → Set
uₗ ⊆ uᵣ = Universe.level uₗ ≤ Universe.level uᵣ

infixl 10 _⊔ᵤ_ 
_⊔ᵤ_  : Universe → Universe → Universe
(univ l₁) ⊔ᵤ (univ l₂) = univ (l₁ ⊔ₙ l₂)

univ₀ : Universe
univ₀ = univ 0

liftUniv : ℕ → Universe → Universe
liftUniv n (univ l) = univ (n + l)

lsuc : Universe → Universe
lsuc = liftUniv 1