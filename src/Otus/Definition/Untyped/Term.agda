module Otus.Definition.Untyped.Term where

open import Data.Nat
open import Otus.Definition.Universe.Base



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
    _,_ : Substitution → Term → Substitution
    _∘_ : Substitution → Substitution → Substitution

idₛ : Substitution
idₛ = drop 0

    

