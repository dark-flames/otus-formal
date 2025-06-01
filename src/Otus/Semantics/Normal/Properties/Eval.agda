{-# OPTIONS --without-K --safe #-}
module Otus.Semantics.Normal.Properties.Eval where

open import Otus.Utils
open import Otus.Syntax
open import Otus.Semantics.Normal.Domain
open import Otus.Semantics.Normal.Eval
open import Otus.Semantics.Normal.Quote

private
  variable
    Γ₁ Γ₂ : Context
    x y : ℕ
    γ₁ γ₂  : Substitution
    a₁ a₂ : Term
    t₁ t₂ u₁ u₂ v₁ v₂ : Value
    E₁ E₂ e₁ e₂ : Closure
    p₁ p₂ : Arguments
    ρ₁ ρ₂ θ₁ θ₂ : Env

envLenCong : ρ₁ ≡ ρ₂ 
    → ∥ ρ₁ ∥≡ x → ∥ ρ₂ ∥≡ y 
    → x ≡ y
appCong : t₁ ≡ t₂ → u₁ ≡ u₂ 
    → App⟨ t₁ ∣ u₁ ⟩⇝ v₁ → App⟨ t₂ ∣ u₂ ⟩⇝ v₂ 
    → v₁ ≡ v₂
natElimCong : E₁ ≡ E₂ → t₁ ≡ t₂ → e₁ ≡ e₂ → u₁ ≡ u₂
    → NatElim⟨ E₁ ∣ t₁ ∣ e₁ ∣ u₁ ⟩⇝ v₁ → NatElim⟨ E₂ ∣ t₂ ∣ e₂ ∣ u₂ ⟩⇝ v₂ 
    → v₁ ≡ v₂
evalCtxCong : Γ₁ ≡ Γ₂ → ρ₁ ≡ ρ₂
    → ↑ Γ₁ ⇝ ρ₁ → ↑ Γ₂ ⇝ ρ₂ 
    → ρ₁ ≡ ρ₂
evalSbCong : γ₁ ≡ γ₂ → ρ₁ ≡ ρ₂
    → ⟦ γ₁ ⟧ˢ ρ₁ ⇝ θ₁ → ⟦ γ₂ ⟧ˢ ρ₂ ⇝ θ₂ 
    → θ₁ ≡ θ₂
evalCong : a₁ ≡ a₂ → ρ₁ ≡ ρ₂
    → ⟦ a₁ ⟧ ρ₁ ⇝ t₁ → ⟦  a₂ ⟧ ρ₂ ⇝ t₂ 
    → t₁ ≡ t₂
evalClosureCong : e₁ ≡ e₂ → p₁ ≡ p₂
  → ⟦ e₁ ⟧⇐ p₁ ⇝ t₁ → ⟦ e₂ ⟧⇐ p₂ ⇝ t₂
  → t₁ ≡ t₂


-- envLenCong : ρ₁ ≡ ρ₂ 
--    → ∥ ρ₁ ∥≡ x → ∥ ρ₂ ∥≡ y 
--    → x ≡ y
envLenCong refl p₁ p₂ with p₁ | p₂
... | ESEmpty | ESEmpty = refl
... | ESExt p₁' | ESExt p₂' = cong suc (envLenCong refl p₁' p₂')


-- appCong : t₁ ≡ t₂ → u₁ ≡ u₂ 
--     → App⟨ t₁ ∣ u₁ ⟩⇝ v₁ → App⟨ t₂ ∣ u₂ ⟩⇝ v₂ 
--     → v₁ ≡ v₂
appCong refl refl (EAppBeta p₁) (EAppBeta p₂) = evalClosureCong refl refl p₁ p₂
appCong refl refl (EAppN p₁) (EAppN p₂) = 
  cong (λ x → ↑ NApp _ _ ∷ x) (evalClosureCong refl refl p₁ p₂)

-- natElimCong : E₁ ≡ E₂ → t₁ ≡ t₂ → e₁ ≡ e₂ → u₁ ≡ u₂
--     → NatElim⟨ E₁ ∣ t₁ ∣ e₁ ∣ u₁ ⟩⇝ v₁ → NatElim⟨ E₂ ∣ t₂ ∣ e₂ ∣ u₂ ⟩⇝ v₂ 
--     → v₁ ≡ v₂
natElimCong refl refl refl refl ENatElimZero ENatElimZero = refl
natElimCong refl refl refl refl (ENatElimSucc p₁ q₁) (ENatElimSucc p₂ q₂) = 
  evalClosureCong refl (cong₂ [_,,_]ₐ refl (natElimCong refl refl refl refl p₁ p₂)) q₁ q₂
natElimCong refl refl refl refl (ENatElimN p₁) (ENatElimN p₂) = 
  cong (λ x → ↑ NNatElim _ _ _ _ ∷ x) (evalClosureCong refl refl p₁ p₂)

-- evalCtxCong : Γ₁ ≡ Γ₂ → ρ₁ ≡ ρ₂
--     → ↑ Γ₁ ⇝ ρ₁ → ↑ Γ₂ ⇝ ρ₂ 
--     → ρ₁ ≡ ρ₂
evalCtxCong refl refl p₁ p₂ = refl

-- evalSbCong : γ₁ ≡ γ₂ → ρ₁ ≡ ρ₂
--     → ⟦ γ₁ ⟧ˢ ρ₁ ⇝ θ₁ → ⟦ γ₂ ⟧ˢ ρ₂ ⇝ θ₂ 
--     → θ₁ ≡ θ₂
evalSbCong refl refl ESbId ESbId = refl
evalSbCong refl refl (ESbDropₛ p₁) (ESbDropₛ p₂) = ++≡-inv (evalSbCong refl refl p₁ p₂)
    where
      ++≡-inv : ∀ {θ₁ θ₂ : Env} {t₁ t₂ : Value} → θ₁ ++ t₁ ≡ θ₂ ++ t₂ → θ₁ ≡ θ₂
      ++≡-inv {_} {_} {_} {_} refl = refl
evalSbCong refl refl (ESbExt p₁ q₁) (ESbExt p₂ q₂) = 
  cong₂ _++_ (evalSbCong refl refl p₁ p₂) (evalCong refl refl q₁ q₂)
evalSbCong refl refl (ESbComp p₁ q₁) (ESbComp p₂ q₂) = 
  evalSbCong refl (evalSbCong refl refl p₁ p₂) q₁ q₂

-- evalCong : a₁ ≡ a₂ → ρ₁ ≡ ρ₂
--     → ⟦ a₁ ⟧ ρ₁ ⇝ t₁ → ⟦  a₂ ⟧ ρ₂ ⇝ t₂ 
--     → t₁ ≡ t₂
evalCong refl refl ETmVarᶻ ETmVarᶻ = refl
evalCong refl refl (ETmVarˢ p₁ u) (ETmVarˢ p₂ .u) = evalCong refl refl p₁ p₂
evalCong refl refl (ETmPi p₁ B) (ETmPi p₂ .B) = 
  cong₂ VPi (evalCong refl refl p₁ p₂) refl
evalCong refl refl ETmLam ETmLam = refl
evalCong refl refl (ETmApp p₁ q₁ r₁) (ETmApp p₂ q₂ r₂) = 
  appCong (evalCong refl refl p₁ p₂) (evalCong refl refl q₁ q₂) r₁ r₂
evalCong refl refl ETmNat ETmNat = refl
evalCong refl refl ETmZero ETmZero = refl
evalCong refl refl (ETmSucc p₁) (ETmSucc p₂) = 
  cong VSucc (evalCong refl refl p₁ p₂)
evalCong refl refl (ETmNatElim p₁ q₁ r₁) (ETmNatElim p₂ q₂ r₂) = 
  natElimCong refl (evalCong refl refl p₁ p₂) refl (evalCong refl refl q₁ q₂) r₁ r₂
evalCong refl refl (ETmSubst p₁ q₁) (ETmSubst p₂ q₂) = 
  evalCong refl (evalSbCong refl refl p₁ p₂) q₁ q₂
evalCong refl refl ETmUniv ETmUniv = refl

-- evalClosureCong : e₁ ≡ e₂ → p₁ ≡ p₂
--   → ⟦ e₁ ⟧⇐ p₁ ⇝ t₁ → ⟦ e₂ ⟧⇐ p₂ ⇝ t₂
--   → t₁ ≡ t₂
evalClosureCong refl refl (EClosure₁ p₁) (EClosure₁ p₂) = 
  evalCong refl refl p₁ p₂
evalClosureCong refl refl (EClosure₂ p₁) (EClosure₂ p₂) = 
  evalCong refl refl p₁ p₂

appConv : v₁ ≡ v₂ → App⟨ t₁ ∣ u₁ ⟩⇝ v₁ → App⟨ t₁ ∣ u₁ ⟩⇝ v₂
appConv refl = id

