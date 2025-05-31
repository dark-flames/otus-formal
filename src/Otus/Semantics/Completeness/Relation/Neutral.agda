{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Neutral where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER

Ne : Rel Neutral 0ℓ
Ne = λ { n₁ n₂ → (x : ℕ) → Σ[ a ∈ Term ] ⌈ n₁ ⌉ⁿ x ≡ᵣ a × ⌈ n₂ ⌉ⁿ x ≡ᵣ a }

open IsPartialEquivalence {{...}} public

instance
  perNe : IsPartialEquivalence Ne
  sym {{ perNe }} p = λ { n → (
      let res , quoteL , quoteR = p n 
      in res , quoteR , quoteL
    ) }
  trans {{ perNe }} p q = λ { n → (
      let 
        resP , quoteP₁ , quoteP₂ = p n 
        resQ , quoteQ₁ , quoteQ₂ = q n 
      in {!   !} , {!   !} , {!   !}
    ) }