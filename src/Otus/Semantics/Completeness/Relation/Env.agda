{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Completeness.Relation.Env where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal
open import Otus.Semantics.Completeness.Relation.PER
open import Otus.Semantics.Completeness.Relation.Neutral

private
  variable
    Γ : Context
    ρ₁ ρ₂ : Env
    t₁ t₂ : Value

data PEREnv : Context → Rel Env 0ℓ where
  PEREnvEmpty : [] ~ [] ∈ᵣ PEREnv ε
  -- PEREnvExt : ρ₁ ~ ρ₂ ∈ᵣ PEREnv Γ → t₁ ~ t₂ ∈ 
  --  → 