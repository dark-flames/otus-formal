{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Normal where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER

PERNf : Rel Normal 0ℓ
PERNf = λ { p₁ p₂ → (x : ℕ) → Σ[ a ∈ Term ] ⌈ p₁ ⌉ x ≡ᵣ a × ⌈ p₂ ⌉ x ≡ᵣ a }


open IsPartialEquivalence {{...}}

instance
  perNf : IsPartialEquivalence PERNf
  sym {{ perNf }} p = λ { n → (
      let res , quoteL , quoteR = p n 
      in res , quoteR , quoteL
    ) }
  trans {{ perNf }} p q = λ { n → (
      let 
        resP , quoteP₁ , quoteP₂ = p n 
        resQ , quoteQ₁ , quoteQ₂ = q n 
        resEq = quoteCong refl refl quoteQ₁ quoteP₂
      in resP , quoteP₁ , quoteNfConv resEq quoteQ₂
    )}

Nf : PER Normal 0ℓ
Nf = record {rel = PERNf ; isPER = perNf}