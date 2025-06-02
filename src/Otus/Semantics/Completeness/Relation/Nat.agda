{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Nat where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER
open import Otus.Semantics.Completeness.Relation.Neutral

private
  variable
    t u v : Value
    n m : Neutral

data PERNat : Rel Value 0ℓ where
  PERZero : VZero ~ VZero ∈ᵣ PERNat
  PERSuc : t ~ u ∈ᵣ PERNat
    → VSucc t ~ VSucc u ∈ᵣ PERNat
  PERNatRefl : n ~ m ∈ Ne
    → ↑ n ∷ VNat ~ ↑ m ∷ VNat ∈ᵣ PERNat


open IsPartialEquivalence {{...}}
private
  perNatSym : t ~ u ∈ᵣ PERNat → u ~ t ∈ᵣ PERNat
  perNatSym p with p
  ...| PERZero = PERZero
  ...| PERSuc q = PERSuc (perNatSym q)
  ...| PERNatRefl q = PERNatRefl (sym q)

  perNatTrans : t ~ u ∈ᵣ PERNat → u ~ v ∈ᵣ PERNat → t ~ v ∈ᵣ PERNat
  perNatTrans p q with p | q
  ...| PERZero | PERZero = PERZero
  ...| PERSuc p' | PERSuc q' = PERSuc (perNatTrans p' q')
  ...| PERNatRefl p' | PERNatRefl q' = PERNatRefl (trans p' q')

instance
  perNat : IsPartialEquivalence PERNat
  sym {{ perNat }} = perNatSym
  trans {{ perNat }} = perNatTrans 

⟦Nat⟧ : PER Value 0ℓ
⟦Nat⟧ = record {rel = PERNat ; isPER = perNat }