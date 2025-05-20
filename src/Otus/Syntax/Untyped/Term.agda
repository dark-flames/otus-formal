{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Term where

open import Otus.Utils
open import Otus.Syntax.Untyped.Universe

infixl 9 _◀_
infixl 8 _∘_
infixl 11 _∙_
infixl 10 _[_]ₑ

data Substitution : Set

data Term : Set where
    Var : ℕ → Term
    
    Pi : Term → Term → Term
    Lam : Term → Term
    _∙_ : Term → Term → Term
    Nat : Term
    Zero : Term
    Succ : Term → Term
    NatElim : Term → Term → Term → Term → Term
    Univ : ULevel → Term
    _[_]ₑ : Term → Substitution → Term

data Substitution where
    drop : ℕ → Substitution
    _◀_ : Substitution → Term → Substitution
    _∘_ : Substitution → Substitution → Substitution

idₛ : Substitution
idₛ = drop 0

lift : Substitution → Substitution
lift γ = (γ ∘ drop 1) ◀ Var 0