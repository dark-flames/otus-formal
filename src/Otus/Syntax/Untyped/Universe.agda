{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Universe where

data ULevel : Set where
    lzero : ULevel
    lsuc  : ULevel → ULevel

infixl 6 _⊔_ 

_⊔_  : ULevel → ULevel → ULevel
lzero ⊔ l₂ = l₂
(lsuc l₁) ⊔ lzero = lsuc l₁
(lsuc l₁) ⊔ (lsuc l₂) = lsuc (l₁ ⊔ l₂)