{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Properties where

open import Otus.Syntax.Untyped.Universe
open import Otus.Syntax.Untyped.Context
open import Otus.Syntax.Untyped.Term

open import Otus.Utils

open PropositionalEq
open ≡-Reasoning

◁-cong : ∀ {Γ Δ : Context} → {A B : Type} → Γ ≡ Δ → A ≡ B → Γ ◁ A ≡ Δ ◁ B
◁-cong refl refl = refl

⧺-identity : {Γ : Context}  → ε ⧺ Γ ≡ Γ
⧺-identity {ε}  = refl
⧺-identity {Γ ◁ A} = ◁-cong (⧺-identity {Γ}) refl

Γ⧺-cong : ∀ {Δ Ξ : Context} (Γ : Context) → Δ ≡ Ξ → Γ ⧺ Δ ≡ Γ ⧺ Ξ
Γ⧺-cong _ refl = refl

⧺Γ-cong : ∀ {Δ Ξ : Context} (Γ : Context) → Δ ≡ Ξ → Δ ⧺ Γ ≡ Ξ ⧺ Γ
⧺Γ-cong _ refl = refl

Γ⧺-ext : ∀ (Γ Δ : Context) → {B : Type} → Γ ⧺ Δ ◁ B ≡ (Γ ⧺ Δ) ◁ B
Γ⧺-ext Γ ε = refl
Γ⧺-ext Γ (Δ ◁ A) {B} = begin
    Γ ⧺ Δ ◁ A ◁ B
  ≡⟨⟩ 
    (Γ ⧺ Δ) ◁ A ◁ B
  ≡⟨ ◁-cong ( Γ⧺-ext Γ Δ ) refl ⟩
    (Γ ⧺ Δ ◁ A) ◁ B
  ∎

⧺-assoc : ∀ {Γ : Context} → (Δ Ξ : Context)  → Γ ⧺ Δ ⧺ Ξ ≡ Γ ⧺ (Δ ⧺ Ξ)
⧺-assoc {Γ} Δ ε  = refl 
⧺-assoc {Γ} Δ (Ξ ◁ C) = begin
    Γ ⧺ Δ ⧺ Ξ ◁ C
  ≡⟨⟩ 
    (Γ ⧺ Δ ⧺ Ξ) ◁ C
  ≡⟨ ◁-cong (⧺-assoc Δ Ξ) refl ⟩ 
    (Γ ⧺ (Δ ⧺ Ξ)) ◁ C
  ≡⟨⟩ 
    Γ ⧺ (Δ ⧺ Ξ) ◁ C
  ≡⟨⟩ 
    Γ ⧺ (Δ ⧺ Ξ ◁ C)
  ∎
 