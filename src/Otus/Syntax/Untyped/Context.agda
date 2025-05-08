{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Context where

open import Otus.Syntax.Untyped.Term

infixl 30 _,_

data Context : Set where
    ε : Context
    _,_ : Context → Term → Context

infixl 29 _⧺_


_⧺_ : Context → Context → Context
Γ ⧺ ε = Γ
Γ ⧺ Δ , A = (Γ ⧺ Δ) , A