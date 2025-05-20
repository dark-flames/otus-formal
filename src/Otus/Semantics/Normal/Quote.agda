{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Quote where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal.Domain
open import Otus.Semantics.Normal.Eval

private
  variable
    l : ULevel
    x y : ℕ
    Γ : Context
    γ δ : Substitution
    A B f a : Term
    V W u v w : Value
    n m : Neutral
    p : Normal
    C c : Closure
    ρ ρ₁ ρ₂ ρ₃ : Env

infix 6 ⌈_⌉_≡_ ⌈_⌉ⁿ_≡_ ⌈_⌉ᵗʸ_≡_

data ⌈_⌉_≡_ : Normal → ℕ → Term → Set
data ⌈_⌉ⁿ_≡_ : Neutral → ℕ → Term → Set
data ⌈_⌉ᵗʸ_≡_ : VType → ℕ → Term → Set


data ⌈_⌉_≡_ where
  RbLam : App⟨ v ∣ ↑ NVar x ∷ V ⟩⇝ w → ⟦ C ⟧⇐ ↑ NVar x ∷ V ⇝ W → ⌈ ↓ w ∷ W ⌉ x ≡ a
    → ⌈ ↓ v ∷ VPi V C ⌉ x ≡ Lam a
  RbTy : ⌈ V ⌉ᵗʸ x ≡ A
    → ⌈ ↓ V ∷ VU l ⌉ x ≡ A


data ⌈_⌉ⁿ_≡_ where
  RbNVar : ⌈ NVar y ⌉ⁿ x ≡ Var (x ∸ (1 + y))
  RbNApp : ⌈ n ⌉ⁿ x ≡ f → ⌈ p ⌉ x ≡ a
      → ⌈ NApp n p  ⌉ⁿ x ≡ f ∙ a

data ⌈_⌉ᵗʸ_≡_ where
  RbNTy : ⌈ n ⌉ⁿ x ≡ A
      → ⌈ ↑ n ∷ V ⌉ᵗʸ x ≡ A
  RbU : ⌈ VU l ⌉ᵗʸ x ≡ U l
  RbPi : ⌈ V ⌉ᵗʸ x ≡ A → ⟦ C ⟧⇐ ↑ NVar x ∷ V ⇝ W → ⌈ W ⌉ᵗʸ 1 + x ≡ B
      → ⌈ VPi V C ⌉ᵗʸ x ≡ Pi A B