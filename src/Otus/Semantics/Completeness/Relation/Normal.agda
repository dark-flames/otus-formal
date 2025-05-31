{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Normal where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER

Nf : Rel Normal 0ℓ
Nf = λ { p₁ p₂ → (x : ℕ) → Σ[ a ∈ Term ] ⌈ p₁ ⌉ x ≡ᵣ a × ⌈ p₂ ⌉ x ≡ᵣ a }