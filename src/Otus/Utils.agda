{-# OPTIONS --without-K --safe #-}

module Otus.Utils where

open import Data.Nat using (ℕ; suc; zero; _+_; _∸_) public
open import Data.Nat.Properties using (+-suc) public
open import Data.Product public
open import Data.Unit using (⊤; tt) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; J; cong) public
open import Function.Base using (id) public

proj₁₂ : ∀ { A B C D : Set } → A × B → C × D → A × D
proj₁₂ ( a , _ ) ( _ , d ) = a , d

module FunComp where
  open import Function.Base using (_∘_) public


suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
suc-+ m    zero = refl
suc-+ m (suc n) = refl