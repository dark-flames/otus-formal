{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Universe.Base where

data ULevel : Set where
  lzero : ULevel
  lsuc  : ULevel → ULevel

infixl 4 _≤ₗ_
data _≤ₗ_ : ULevel → ULevel → Set where
  lz≤ln : ∀ {l}    → lzero ≤ₗ l
  ls≤ls : ∀ {l₁ l₂} → l₁ ≤ₗ l₂ → lsuc l₁ ≤ₗ lsuc l₂

infixl 10 _⊔_ 

lBottom : ULevel
lBottom = lzero

_⊔_  : ULevel → ULevel → ULevel
lzero ⊔ l₂            = l₂
(lsuc l₁) ⊔ lzero     = lsuc l₁
(lsuc l₁) ⊔ (lsuc l₂) = lsuc (l₁ ⊔ l₂)