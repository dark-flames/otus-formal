{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Eval where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal.Domain 

private
  variable
    l : ULevel
    x : ℕ
    Γ : Context
    γ δ : Substitution
    A B f a b c d : Term
    R T U V r t u v w : Value
    n m : Neutral
    E e : Closure
    ρ ρ₁ ρ₂ ρ₃ : Env

infix 6 ↑_⇝_ ⟦_⟧ˢ_⇝_ ⟦_⟧_⇝_ ⟦_⟧⇐_⇝_ App⟨_∣_⟩⇝_ NatElim⟨_∣_∣_∣_⟩⇝_

data ∥_∥≡_ : Env → ℕ → Set
data ↑_⇝_ : Context → Env → Set
data  ⟦_⟧ˢ_⇝_ : Substitution → Env → Env → Set
data  ⟦_⟧_⇝_ : Term → Env → Value → Set
data  ⟦_⟧⇐_⇝_ : Closure → Arguments → Value → Set

---- eliminator
data App⟨_∣_⟩⇝_ : Value → Value → Value → Set
data NatElim⟨_∣_∣_∣_⟩⇝_ : Closure → Value → Closure → Value → Value → Set

data ∥_∥≡_ where
  ESEmpty : ∥ [] ∥≡ 0
  ESExt : ∥ ρ ∥≡ x
    → ∥ ρ ++ u ∥≡ (1 + x)

data ↑_⇝_ where
  ECEmpty : ↑ ε ⇝ []
  ECExt : ↑ Γ ⇝ ρ → ⟦ A ⟧ ρ ⇝ T → ∥ ρ ∥≡ x
    → ↑ Γ ◁ A ⇝ ρ ++ (↑ NVar x ∷ T)

data  ⟦_⟧ˢ_⇝_  where
  ESbId : ⟦ idₛ ⟧ˢ ρ ⇝ ρ
  ESbDropₛ : ⟦ drop x ⟧ˢ ρ₁ ⇝ ρ₂ ++ u
    → ⟦ drop (1 + x) ⟧ˢ ρ₁ ⇝ ρ₂
  ESbExt : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ a ⟧ ρ₁ ⇝ u
    → ⟦ γ ◀ a ⟧ˢ ρ₁ ⇝ ρ₂ ++ u
  ESbComp : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ δ ⟧ˢ ρ₂ ⇝ ρ₃
    → ⟦ δ ∘ γ ⟧ˢ ρ₁ ⇝ ρ₃

data  ⟦_⟧_⇝_ where
  ETmVarᶻ : ⟦ Var 0 ⟧ ρ ++ t ⇝ t
  ETmVarˢ : ⟦ Var x ⟧ ρ ⇝ t → (u : Value)
    → ⟦ Var (1 + x) ⟧ ρ ++ u ⇝ t
  ETmPi : ⟦ A ⟧ ρ ⇝ T → (B : Term)
    → ⟦ Pi A B ⟧ ρ ⇝ VPi T (⟨ B ⟩ ρ)
  ETmLam : ⟦ Lam a ⟧ ρ ⇝ VLam (⟨ a ⟩ ρ)
  ETmApp : ⟦ f ⟧ ρ ⇝ t → ⟦ a ⟧ ρ ⇝ u → App⟨ t ∣ u ⟩⇝ v
    → ⟦ f ∙ a ⟧ ρ ⇝ v
  ETmNat : ⟦ Nat ⟧ ρ ⇝ VNat
  ETmZero : ⟦ Zero ⟧ ρ ⇝ VZero
  ETmSucc : ⟦ a ⟧ ρ ⇝ t 
    → ⟦ Succ a ⟧ ρ ⇝ VSucc t
  ETmNatElim : ⟦ a ⟧ ρ ⇝ t → ⟦ c ⟧ ρ ⇝ u → NatElim⟨ ⟨ A ⟩ ρ ∣ t ∣ ⟨ b ⟩ ρ ∣ u ⟩⇝ v
    → ⟦ NatElim A a b d ⟧ ρ  ⇝ v 
  ETmSubst : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ a ⟧ ρ₂ ⇝ t
    → ⟦ a [ γ ]ₑ ⟧ ρ₁ ⇝ t
  ETmUniv : ⟦ Univ l ⟧ ρ ⇝ VUniv l

data  ⟦_⟧⇐_⇝_ where
  EClosure₁ : ⟦ a ⟧ ρ ++ t ⇝ u
    → ⟦ ⟨ a ⟩ ρ ⟧⇐ [ t ]ₐ ⇝ u
  EClosure₂ : ⟦ a ⟧ ρ ++ t ++ u ⇝ v
    → ⟦ ⟨ a ⟩ ρ ⟧⇐  [ t ,, u ]ₐ ⇝ v

data App⟨_∣_⟩⇝_ where
  EAppBeta : ⟦ e ⟧⇐ [ t ]ₐ ⇝ u
    → App⟨ VLam e ∣ t ⟩⇝ u
  EAppN : ⟦ E ⟧⇐ [ t ]ₐ ⇝ U
    → App⟨ ↑ n ∷ VPi T E ∣ t ⟩⇝ ↑ NApp n (↓ t ∷ T) ∷ U

data NatElim⟨_∣_∣_∣_⟩⇝_ where
  ENatElimZero : NatElim⟨ E ∣ t ∣ e ∣ VZero ⟩⇝ t
  ENatElimSucc : NatElim⟨ E ∣ t ∣ e ∣ u ⟩⇝ v → ⟦ e ⟧⇐ [ u ,, v ]ₐ ⇝ w
    → NatElim⟨ E ∣ t ∣ e ∣ VSucc u ⟩⇝ w
  ENatElimN : ⟦ E ⟧⇐ [ ↑ n ∷ VNat ]ₐ ⇝ T
    → NatElim⟨ E ∣ t ∣ e ∣ ↑ n ∷ VNat ⟩⇝ ↑ NNatElim E t e n ∷ T
