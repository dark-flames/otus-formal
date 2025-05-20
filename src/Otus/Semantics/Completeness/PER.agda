{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.PER where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal


infix 6 _~_∈Ne _~_∈Nf _~_∈Ty

_~_∈Ne : Neutral → Neutral → Set
n₁ ~ n₂ ∈Ne  = (x : ℕ) → Σ[ a ∈ Term ] ⌈ n₁ ⌉ⁿ x ≡ a × ⌈ n₂ ⌉ⁿ x ≡ a

_~_∈Nf : Normal → Normal → Set 
p₁ ~ p₂ ∈Nf = (x : ℕ) → Σ[ a ∈ Term ] ⌈ p₁ ⌉ x ≡ a × ⌈ p₂ ⌉ x ≡ a

_~_∈Ty : VType → VType → Set
V₁ ~ V₂ ∈Ty = (x : ℕ) → Σ[ A ∈ Term ] ⌈ V₁ ⌉ᵗʸ x ≡ A × ⌈ V₂ ⌉ᵗʸ x ≡ A