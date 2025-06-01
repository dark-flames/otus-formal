{-# OPTIONS --without-K --safe #-}

module Otus.Utils where

open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _≤_) public
open import Data.Nat.Properties using (+-suc) public
open import Data.Product public
open import Data.Unit using (⊤; tt) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; J; cong; cong₂) public
open import Function.Base using (id) public
open import Relation.Binary using (Rel; REL; _⇔_; IsPartialEquivalence) public
open import Level using (Level; 0ℓ) public

module FunComp where
  open import Function.Base using (_∘_) public

proj₁₂ : ∀ { A B C D : Set } → A × B → C × D → A × D
proj₁₂ ( a , _ ) ( _ , d ) = a , d


suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
suc-+ m    zero = refl
suc-+ m (suc n) = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} {d₁ d₂ : D}
      → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
cong₄ f refl refl refl refl = refl


