{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Quote where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal.Domain
open import Otus.Semantics.Normal.Eval

private
  variable
    l : Universe
    x y : ℕ
    Γ : Context
    γ δ : Substitution
    A B f a b c : Term
    T U V W t u v w : Value
    n m : Neutral
    p : Normal
    E e : Closure
    ρ ρ₁ ρ₂ ρ₃ : Env

infix 6 ⌈_⌉_≡ᵣ_ ⌈_⌉ⁿ_≡ᵣ_ ⌈_⌉ᵗʸ_≡ᵣ_

data ⌈_⌉_≡ᵣ_ : Normal → ℕ → Term → Set
data ⌈_⌉ⁿ_≡ᵣ_ : Neutral → ℕ → Term → Set
data ⌈_⌉ᵗʸ_≡ᵣ_ : VType → ℕ → Term → Set


data ⌈_⌉_≡ᵣ_ where
  RbLam : App⟨ t ∣ ↑ NVar x ∷ T ⟩⇝ u → ⟦ E ⟧⇐ [ ↑ NVar x ∷ T ]ₐ ⇝ U → ⌈ ↓ u ∷ U ⌉ x ≡ᵣ a
      → ⌈ ↓ t ∷ VPi T E ⌉ x ≡ᵣ Lam a
  RbZero : ⌈ ↓ VZero ∷ VNat ⌉ x ≡ᵣ Zero
  RbSucc : ⌈ ↓ t ∷ VNat ⌉ x ≡ᵣ a
      → ⌈ ↓ VSucc t ∷ VNat ⌉ x ≡ᵣ Succ a
  RbNNat : ⌈ n ⌉ⁿ x ≡ᵣ a
      → ⌈ ↓ (↑ n ∷ T) ∷ VNat ⌉ x ≡ᵣ a
  RbTy : ⌈ V ⌉ᵗʸ x ≡ᵣ A
      → ⌈ ↓ V ∷ VUniv l ⌉ x ≡ᵣ A


data ⌈_⌉ⁿ_≡ᵣ_ where
  RbNVar : ⌈ NVar y ⌉ⁿ x ≡ᵣ Var (x ∸ (1 + y))
  RbNApp : ⌈ n ⌉ⁿ x ≡ᵣ f → ⌈ p ⌉ x ≡ᵣ a
      → ⌈ NApp n p  ⌉ⁿ x ≡ᵣ f ∙ a
  RbNNatElim : ⟦ E ⟧⇐ [ ↑ NVar x ∷ VNat ]ₐ ⇝ U → ⌈ U ⌉ᵗʸ 1 + x ≡ᵣ A
      → ⟦ E ⟧⇐ [ VZero ]ₐ ⇝ V → ⌈ ↓ t ∷ V ⌉ x ≡ᵣ a
      → ⟦ E ⟧⇐ [ VSucc (↑ NVar x ∷ VNat) ]ₐ ⇝ W → ⟦ e ⟧⇐ [ ↑ NVar x ∷ VNat ,, ↑ NVar (1 + x) ∷ U ]ₐ ⇝ u → ⌈ ↓ u ∷ W ⌉ 2 + x ≡ᵣ b
      → ⌈ n ⌉ⁿ x ≡ᵣ c
      → ⌈ NNatElim E t e n  ⌉ⁿ x ≡ᵣ NatElim A a b c


data ⌈_⌉ᵗʸ_≡ᵣ_ where
  RbNTy : ⌈ n ⌉ⁿ x ≡ᵣ A
      → ⌈ ↑ n ∷ T ⌉ᵗʸ x ≡ᵣ A
  RbPi : ⌈ T ⌉ᵗʸ x ≡ᵣ A → ⟦ E ⟧⇐ [ ↑ NVar x ∷ T ]ₐ ⇝ U → ⌈ U ⌉ᵗʸ 1 + x ≡ᵣ B
      → ⌈ VPi T E ⌉ᵗʸ x ≡ᵣ Pi A B
  RbNat : ⌈ VNat ⌉ᵗʸ x ≡ᵣ Nat
  RbUniv : ⌈ VUniv l ⌉ᵗʸ x ≡ᵣ Univ l
  