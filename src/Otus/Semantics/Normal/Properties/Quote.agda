{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Properties.Quote where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal.Domain
open import Otus.Semantics.Normal.Eval
open import Otus.Semantics.Normal.Quote
open import Otus.Semantics.Normal.Properties.Eval


private
  variable
    l : ULevel
    x y : ℕ
    a₁ a₂ : Term
    t₁ t₂ : Value
    n₁ n₂ : Neutral
    p₁ p₂ : Normal

quoteCong : p₁ ≡ p₂ → x ≡ y
    → ⌈ p₁ ⌉ x ≡ᵣ a₁ → ⌈ p₂ ⌉ y ≡ᵣ a₂ 
    → a₁ ≡ a₂
quoteNeCong : n₁ ≡ n₂ → x ≡ y
    → ⌈ n₁ ⌉ⁿ x ≡ᵣ a₁ → ⌈ n₂ ⌉ⁿ y ≡ᵣ a₂ 
    → a₁ ≡ a₂
quoteTyCong : t₁ ≡ t₂ → x ≡ y
    → ⌈ t₁ ⌉ᵗʸ x ≡ᵣ a₁ → ⌈ t₂ ⌉ᵗʸ y ≡ᵣ a₂ 
    → a₁ ≡ a₂

-- quoteCong : p₁ ≡ p₂ → x ≡ y
--     → ⌈ p₁ ⌉ x ≡ᵣ a₁ → ⌈ p₂ ⌉ y ≡ᵣ a₂ 
--     → a₁ ≡ a₂
quoteCong refl refl (RbLam p₁ q₁ r₁) (RbLam p₂ q₂ r₂) = let
    pEq = appCong refl refl p₁ p₂
    CEq = evalClosureCong refl refl q₁ q₂
  in cong Lam (quoteCong (cong₂ ↓_∷_ pEq CEq) refl r₁ r₂)
quoteCong refl refl RbZero RbZero = refl
quoteCong refl refl (RbSucc p₁) (RbSucc p₂) = 
  cong Succ (quoteCong refl refl p₁ p₂)
quoteCong refl refl (RbNNat p₁) (RbNNat p₂) = 
  quoteNeCong refl refl p₁ p₂
quoteCong refl refl (RbTy p₁) (RbTy p₂) = 
  quoteTyCong refl refl p₁ p₂

-- quoteNeCong : n₁ ≡ n₂ → x ≡ y
--     → ⌈ n₁ ⌉ⁿ x ≡ᵣ a₁ → ⌈ n₂ ⌉ⁿ y ≡ᵣ a₂ 
--     → a₁ ≡ a₂
quoteNeCong refl refl RbNVar RbNVar = refl
quoteNeCong refl refl (RbNApp p₁ q₁) (RbNApp p₂ q₂) = 
  cong₂ _∙_ (quoteNeCong refl refl p₁ p₂) (quoteCong refl refl q₁ q₂)
quoteNeCong refl refl (RbNNatElim p₁ q₁ r₁ s₁ t₁ u₁ v₁ w₁) (RbNNatElim p₂ q₂ r₂ s₂ t₂ u₂ v₂ w₂) = let
    UxEq = evalClosureCong refl refl p₁ p₂
    U0Eq = evalClosureCong refl refl r₁ r₂
    argEq = cong₂ [_,,_]ₐ refl (cong₂ ↑_∷_ refl UxEq)
    uEq = evalClosureCong refl argEq u₁ u₂
    USEq = evalClosureCong refl refl t₁ t₂
  in cong₄ NatElim (quoteTyCong UxEq refl q₁ q₂) 
                   (quoteCong (cong₂ ↓_∷_ refl U0Eq) refl s₁ s₂)
                   (quoteCong (cong₂ ↓_∷_ uEq USEq) refl v₁ v₂)
                   (quoteNeCong refl refl w₁ w₂)

-- quoteTyCong : t₁ ≡ t₂ → x ≡ y
--     → ⌈ t₁ ⌉ᵗʸ x ≡ᵣ a₁ → ⌈ t₂ ⌉ᵗʸ y ≡ᵣ a₂ 
--     → a₁ ≡ a₂
quoteTyCong refl refl (RbNTy p₁) (RbNTy p₂) = 
  quoteNeCong refl refl p₁ p₂
quoteTyCong refl refl (RbPi p₁ q₁ r₁) (RbPi p₂ q₂ r₂) = let
    UEq = evalClosureCong refl refl q₁ q₂
  in cong₂ Pi (quoteTyCong refl refl p₁ p₂)
              (quoteTyCong UEq refl r₁ r₂)
quoteTyCong refl refl RbNat RbNat = refl
quoteTyCong refl refl RbUniv RbUniv = refl


quoteNeConv : a₁ ≡ a₂ → ⌈ n₁ ⌉ⁿ x ≡ᵣ a₁ → ⌈ n₁ ⌉ⁿ x ≡ᵣ a₂
quoteNeConv refl = id

quoteNfConv : a₁ ≡ a₂ → ⌈ p₁ ⌉ x ≡ᵣ a₁ → ⌈ p₁ ⌉ x ≡ᵣ a₂
quoteNfConv refl = id