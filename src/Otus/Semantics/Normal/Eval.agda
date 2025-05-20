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
    A B f a : Term
    V W u v w : Value
    n m : Neutral
    C c : Closure
    ρ ρ₁ ρ₂ ρ₃ : Env

infix 6 ↑_⇝_ ⟦_⟧ˢ_⇝_ ⟦_⟧_⇝_ ⟦_⟧⇐_⇝_ App⟨_∣_⟩⇝_

data ∥_∥≡_ : Env → ℕ → Set
data ↑_⇝_ : Context → Env → Set
data  ⟦_⟧ˢ_⇝_ : Substitution → Env → Env → Set
data  ⟦_⟧_⇝_ : Term → Env → Value → Set
data  ⟦_⟧⇐_⇝_ : Closure → Value → Value → Set

---- eliminator
data App⟨_∣_⟩⇝_ : Value → Value → Value → Set

data ∥_∥≡_ where
  ESEmpty : ∥ [] ∥≡ 0
  ESExt : ∥ ρ ∥≡ x
    → ∥ ρ ++ u ∥≡ (1 + x)

data ↑_⇝_ where
  ECEmpty : ↑ ε ⇝ []
  ECExt : ↑ Γ ⇝ ρ → ⟦ A ⟧ ρ ⇝ V → ∥ ρ ∥≡ x
    → ↑ Γ ◁ A ⇝ ρ ++ (↑ NVar x ∷ V)

data  ⟦_⟧ˢ_⇝_  where
  ESbId : ⟦ idₛ ⟧ˢ ρ ⇝ ρ
  ESbDropₛ : ⟦ drop x ⟧ˢ ρ₁ ⇝ ρ₂ ++ v
    → ⟦ drop (1 + x) ⟧ˢ ρ₁ ⇝ ρ₂
  ESbExt : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ a ⟧ ρ₁ ⇝ v
    → ⟦ γ ◀ a ⟧ˢ ρ₁ ⇝ ρ₂ ++ v
  ESbComp : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ δ ⟧ˢ ρ₂ ⇝ ρ₃
    → ⟦ δ ∘ γ ⟧ˢ ρ₁ ⇝ ρ₃

data  ⟦_⟧_⇝_ where
  ETmVarᶻ : ⟦ Var 0 ⟧ ρ ++ v ⇝ v
  ETmVarˢ : ⟦ Var x ⟧ ρ ⇝ v → (w : Value)
    → ⟦ Var (1 + x) ⟧ ρ ++ w ⇝ v
  ETmPi : ⟦ A ⟧ ρ ⇝ V → (B : Term)
    → ⟦ Pi A B ⟧ ρ ⇝ VPi V (⟨ B ⟩ ρ)
  ETmLam : ⟦ Lam a ⟧ ρ ⇝ VLam (⟨ a ⟩ ρ)
  ETmApp : ⟦ f ⟧ ρ ⇝ v → ⟦ a ⟧ ρ ⇝ w → App⟨ v ∣ w ⟩⇝ u
    → ⟦ f ∙ a ⟧ ρ ⇝ u
  ETmSubst : ⟦ γ ⟧ˢ ρ₁ ⇝ ρ₂ → ⟦ a ⟧ ρ₂ ⇝ v
    → ⟦ a [ γ ]ₑ ⟧ ρ₁ ⇝ v
  ETmUniv : ⟦ Univ l ⟧ ρ ⇝ VUniv l

data  ⟦_⟧⇐_⇝_ where
  EClosure : ⟦ a ⟧ ρ ++ v ⇝ w
    → ⟦ ⟨ a ⟩ ρ ⟧⇐ v ⇝ w

data App⟨_∣_⟩⇝_ where
  EAppBeta : ⟦ c ⟧⇐ v ⇝ w
    → App⟨ VLam c ∣ v ⟩⇝ w
  EAppN : ⟦ C ⟧⇐ v ⇝ W
    → App⟨ ↑ n ∷ VPi V C ∣ v ⟩⇝ ↑ (NApp n (↓ v ∷ V)) ∷ W
