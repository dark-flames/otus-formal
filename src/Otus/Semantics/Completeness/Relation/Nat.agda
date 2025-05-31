{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Nat where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER
open import Otus.Semantics.Completeness.Relation.Neutral

private
  variable
    t u : Value
    n m : Neutral

data ⟦Nat⟧ : Rel Value 0ℓ where
  PERZero : VZero ~ VZero ∈ ⟦Nat⟧
  PERSuc : t ~ u ∈ ⟦Nat⟧
    → VSucc t ~ VSucc u ∈ ⟦Nat⟧
  PERNatRefl : n ~ m ∈ Ne
    → ↑ n ∷ VNat ~ ↑ m ∷ VNat ∈ ⟦Nat⟧