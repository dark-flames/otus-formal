{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Domain where

open import Otus.Utils
open import Otus.Syntax.Untyped

private
  variable
    n : ℕ

data Value : Set
data Neutral : Set
data Normal : Set
data Env : Set

VType : Set
VType = Value

infixl 9 ⟨_⟩_ ↑_∷_
infixl 8 ↓_∷_
infixl 7 _++_

data Closure : Set where
  ⟨_⟩_ : Term → Env → Closure

open Closure

data Value where
  VPi  : Value → Closure → Value
  VLam : Closure → Value
  VUniv : ULevel → Value
  ↑_∷_ : Neutral → VType → Value

open Value

data Neutral where
  NVar : ℕ → Neutral
  NApp : Neutral → Normal → Neutral

open Neutral

data Normal where
  ↓_∷_ : Value → VType → Normal

open Normal

data Env where
    [] : Env
    _++_ : Env → Value → Env

open Env