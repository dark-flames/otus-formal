{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Universe where

data ULevel : Set where
    lzero : ULevel
    lsuc  : ULevel → ULevel

infixl 10 _⊔_ 

lBottom : ULevel
lBottom = lzero

_⊔_  : ULevel → ULevel → ULevel
lzero ⊔ l₂ = l₂
(lsuc l₁) ⊔ lzero = lsuc l₁
(lsuc l₁) ⊔ (lsuc l₂) = lsuc (l₁ ⊔ l₂)