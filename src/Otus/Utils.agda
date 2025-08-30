{-# OPTIONS --without-K --safe #-}

module Otus.Utils where

module Relation where
  open import Relation.Binary using (Reflexive; Total; Antisymmetric) public
  open import Relation.Binary using (Rel; REL; _⇔_; IsPartialEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder) public

module Algebra where
  open import Algebra.Definitions using (Idempotent) public

module PropositionalEq where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; J; cong; cong₂) renaming (sym to ≡-sym; trans to ≡-trans; isEquivalence to ≡-isEquivalence) public
  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} {d₁ d₂ : D}
      → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
  cong₄ f refl refl refl refl = refl

module ≡-Reasoning where
  open import Relation.Binary.PropositionalEquality.Properties
  open ≡-Reasoning public 

module Product where
  open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂; swap; uncurry) public

  proj₁₂ : ∀ { A B C D : Set } → A × B → C × D → A × D
  proj₁₂ ( a , _ ) ( _ , d ) = a , d

module Sum where
  open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to ⊎-map) public

module Nat where
  open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _≤_) renaming (_⊔_ to _⊔ₙ_) public
  open import Data.Nat.Properties using (+-suc; ⊔-idem; ≤-refl; m≤n⇒m≤1+n; m∸n+n≡m; m≤m⊔n; m≤n⊔m) public
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
  suc-+ m    zero = refl
  suc-+ m (suc n) = refl

module Unit where
  open import Data.Unit using (⊤; tt) public

module Function where
  open import Function.Base using (id) public

module FunComp where
  open import Function.Base using (_∘_) public

module Level where
  open import Agda.Primitive using (_⊔_; lsuc ; lzero) public
  open import Level using (Level; 0ℓ) public

open Nat public


