{-# OPTIONS --without-K #-}
module Otus.Semantics.Domain where

open import Otus.Utils
open import Otus.Syntax.Untyped

private
  variable
    n : ℕ

data Value : Set
data Neutral : Set
data Normal : Set
data Env : ℕ → Set

VType : Set
VType = Value

data Closure : Set where
  ⟨_⟩_ : Env n → Term → Closure

data Value where
  VPi  : Value → Closure → Value
  VLam : Closure → Value
  U : ULevel → Value
  Relflection : Neutral → VType → Value

data Neutral where
  NVar : ℕ → Neutral
  NApp : Neutral → Normal → Neutral

data Normal where
  Reification : VType → Value → Normal

data Env where
    [] : Env 0
    _++_ : Env n → Value → Env (1 + n)