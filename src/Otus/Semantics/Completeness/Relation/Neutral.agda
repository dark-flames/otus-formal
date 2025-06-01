{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Neutral where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER

PERNe : Rel Neutral 0ℓ
PERNe = λ { n₁ n₂ → (x : ℕ) → Σ[ a ∈ Term ] ⌈ n₁ ⌉ⁿ x ≡ᵣ a × ⌈ n₂ ⌉ⁿ x ≡ᵣ a }

open IsPartialEquivalence {{...}}

instance
  perNe : IsPartialEquivalence PERNe
  sym {{ perNe }} p = λ { n → (
      let res , quoteL , quoteR = p n 
      in res , quoteR , quoteL
    ) }
  trans {{ perNe }} p q = λ { n → (
      let 
        resP , quoteP₁ , quoteP₂ = p n 
        resQ , quoteQ₁ , quoteQ₂ = q n 
        resEq = quoteNeCong refl refl quoteQ₁ quoteP₂
      in resP , quoteP₁ , quoteNeConv resEq quoteQ₂
    )}

Ne : PER Neutral 0ℓ
Ne = record { rel = PERNe ; isPER = perNe }