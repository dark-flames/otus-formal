{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Context where

open import Otus.Syntax.Untyped.Term

infixl 8 _◁_
infixl 7 _⧺_

data Context : Set where
    ε : Context
    _◁_ : Context → Type → Context


_⧺_ : Context → Context → Context
Γ ⧺ ε = Γ
Γ ⧺ Δ ◁ A = (Γ ⧺ Δ) ◁ A