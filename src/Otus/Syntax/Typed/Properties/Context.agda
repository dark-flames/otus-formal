{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.Context where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)

private
  variable
    Γ Δ Ξ : Context
    A B a b : Term
    γ : Substitution