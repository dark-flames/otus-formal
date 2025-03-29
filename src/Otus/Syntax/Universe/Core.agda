module Otus.Syntax.Universe.Core where

data ULevel : Set where
    lzero : ULevel
    lsuc  : ULevel → ULevel

infix 6 _⊔_ 
_⊔_  : ULevel → ULevel → ULevel
lzero ⊔ l₂ = l₂
(lsuc l₁) ⊔ lzero = lsuc l₁
(lsuc l₁) ⊔ (lsuc l₂) = lsuc (l₁ ⊔ l₂)