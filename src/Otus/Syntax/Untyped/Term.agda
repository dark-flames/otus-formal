{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped.Universe

infixl 33 _▶_
infixl 31 _∘_

data Substitution : Set

data Term : Set where
    Var : ℕ → Term
    Lam : Term → Term
    Pi : Term → Term → Term
    _∙_ : Term → Term → Term
    U : ULevel → Term
    _[_]ₑ : Term → Substitution → Term

data Substitution where
    drop : ℕ → Substitution
    _▶_ : Substitution → Term → Substitution
    _∘_ : Substitution → Substitution → Substitution

idₛ : Substitution
idₛ = drop 0

lift : Substitution → Substitution
lift γ = (γ ∘ (drop 1)) ▶ Var 0