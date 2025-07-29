{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Universe.Properties where

open import Otus.Syntax.Untyped.Universe.Base

open import Otus.Utils

open PropositionalEq
open Relation
open Algebra
open Sum
open Product
open Nat
open ≡-Reasoning
--- Universe

⊔ᵤ-idem : (u : Universe) → u ⊔ᵤ u ≡ u
⊔ᵤ-idem (univ l) = cong univ (⊔-idem l)

u₁⊆u₁⊔u₂ : ∀ { u₁ u₂ } → u₁ ⊆ u₁ ⊔ᵤ u₂
u₁⊆u₁⊔u₂ {univ l₁} {univ l₂} = m≤m⊔n l₁ l₂

u₂⊆u₁⊔u₂ : ∀ { u₁ u₂ } → u₂ ⊆ u₁ ⊔ᵤ u₂ 
u₂⊆u₁⊔u₂ {univ l₁} {univ l₂} = m≤n⊔m l₁ l₂
{-

⊔-lzeroʳ : ∀ {l} → l ⊔ lzero ≡ l
⊔-lzeroʳ {lzero} = refl
⊔-lzeroʳ {lsuc l} = refl

⊔-comm : ∀ {l₁ l₂} → l₁ ⊔ l₂ ≡ l₂ ⊔ l₁
⊔-comm {lzero} {l₂} = ≡-sym ⊔-lzeroʳ
⊔-comm {lsuc l₁} {lzero} = refl
⊔-comm {lsuc l₁} {lsuc l₂} = cong lsuc ( ⊔-comm {l₁} {l₂} )

⊔-assoc : ∀ {l₁ l₂ l₃} → (l₁ ⊔ l₂) ⊔ l₃ ≡ l₁ ⊔ (l₂ ⊔ l₃)
⊔-assoc {lzero} {l₂} {l₃} = refl
⊔-assoc {lsuc l₁} {lzero} {l₃} = refl
⊔-assoc {lsuc l₁} {lsuc l₂} {lzero} = refl
⊔-assoc {lsuc l₁} {lsuc l₂} {lsuc l₃} = begin
    (lsuc l₁ ⊔ lsuc l₂) ⊔ lsuc l₃ 
  ≡⟨⟩
    lsuc (l₁ ⊔ l₂) ⊔ lsuc l₃
  ≡⟨⟩
    lsuc (l₁ ⊔ l₂ ⊔ l₃)
  ≡⟨ cong lsuc (⊔-assoc {l₁} {l₂} {l₃})  ⟩
    lsuc (l₁ ⊔ (l₂ ⊔ l₃))
  ≡⟨ refl ⟩
    lsuc l₁ ⊔ (lsuc l₂ ⊔ lsuc l₃)
  ∎  -- cong lsuc (⊔-assoc {l₁} {l₂} {l₃})

≤ₗ-refl : ∀ {l} → l ≤ₗ l
≤ₗ-refl { lzero }  = lz≤ln
≤ₗ-refl { lsuc l } = ls≤ls ≤ₗ-refl

≤ₗ-trans : ∀ {l₁ l₂ l₃} → l₁ ≤ₗ l₂ → l₂ ≤ₗ l₃ → l₁ ≤ₗ l₃
≤ₗ-trans lz≤ln _ = lz≤ln
≤ₗ-trans (ls≤ls r₁) (ls≤ls r₂) = ls≤ls (≤ₗ-trans r₁ r₂)

≤ₗ-reflexive : ∀ {l₁ l₂} → l₁ ≡ l₂ → l₁ ≤ₗ l₂
≤ₗ-reflexive refl = ≤ₗ-refl

≤ₗ-totality : Total _≤ₗ_
≤ₗ-totality lzero l₂ = inj₁ lz≤ln
≤ₗ-totality l₁ lzero = inj₂ lz≤ln
≤ₗ-totality (lsuc l₁) (lsuc l₂) = ⊎-map ls≤ls ls≤ls (≤ₗ-totality l₁ l₂)

≤ₗ-antisym : Antisymmetric _≡_ _≤ₗ_
≤ₗ-antisym lz≤ln lz≤ln = refl
≤ₗ-antisym (ls≤ls r₁) (ls≤ls r₂) = cong lsuc (≤ₗ-antisym r₁ r₂)

≤ₗ-lsucᵣ : ∀ {l₁ l₂} → l₁ ≤ₗ l₂ → l₁ ≤ₗ lsuc l₂
≤ₗ-lsucᵣ lz≤ln = lz≤ln
≤ₗ-lsucᵣ (ls≤ls r) = ls≤ls (≤ₗ-lsucᵣ r)

≤ₗ-diff : ∀ {l₁ l₂} → l₁ ≤ₗ l₂ → Σ[ n ∈ ℕ ] liftUniv l₁ n ≡ l₂
≤ₗ-diff lz≤ln

≤ₗ-isPreorder : IsPreorder _≡_ _≤ₗ_
≤ₗ-isPreorder = record {
    isEquivalence = ≡-isEquivalence;
    reflexive     = ≤ₗ-reflexive;
    trans         = ≤ₗ-trans
  }

≤ₗ-isPartialOrder : IsPartialOrder _≡_ _≤ₗ_
≤ₗ-isPartialOrder = record {
    isPreorder = ≤ₗ-isPreorder;
    antisym    = ≤ₗ-antisym
  }

≤ₗ-isTotalOrder : IsTotalOrder _≡_ _≤ₗ_
≤ₗ-isTotalOrder = record {
    isPartialOrder = ≤ₗ-isPartialOrder;
    total = ≤ₗ-totality
  }
  -}