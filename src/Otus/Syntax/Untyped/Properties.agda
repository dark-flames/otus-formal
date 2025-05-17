{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Untyped.Properties where

open import Otus.Syntax.Untyped.Universe
open import Otus.Syntax.Untyped.Context
open import Otus.Syntax.Untyped.Term

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
--- Universe

⊔-identity : ∀ {l} → l ⊔ l ≡ l
⊔-identity {lzero} = refl
⊔-identity {lsuc l} = cong lsuc (⊔-identity)

⊔-lzeroʳ : ∀ {l} → l ⊔ lzero ≡ l
⊔-lzeroʳ {lzero} = refl
⊔-lzeroʳ {lsuc l} = refl

⊔-comm : ∀ {l₁ l₂} → l₁ ⊔ l₂ ≡ l₂ ⊔ l₁
⊔-comm {lzero} {l₂} = sym ⊔-lzeroʳ
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

--- Context
◁-cong : ∀ { Γ Δ : Context } → { A B : Term } → Γ ≡ Δ → A ≡ B → Γ ◁ A ≡ Δ ◁ B
◁-cong refl refl = refl

⧺-identity : {Γ : Context}  → ε ⧺ Γ ≡ Γ
⧺-identity {ε}  = refl
⧺-identity {Γ ◁ A} = ◁-cong (⧺-identity {Γ}) refl

Γ⧺-cong : ∀ { Δ Ξ : Context } (Γ : Context) → Δ ≡ Ξ → Γ ⧺ Δ ≡ Γ ⧺ Ξ
Γ⧺-cong _ refl = refl

⧺Γ-cong : ∀ { Δ Ξ : Context } (Γ : Context) → Δ ≡ Ξ → Δ ⧺ Γ ≡ Ξ ⧺ Γ
⧺Γ-cong _ refl = refl

Γ⧺-ext : ∀ (Γ Δ : Context) → {B : Term} → Γ ⧺ Δ ◁ B ≡ (Γ ⧺ Δ) ◁ B
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
  ≡⟨ ◁-cong (⧺-assoc Δ Ξ ) refl ⟩ 
    (Γ ⧺ (Δ ⧺ Ξ)) ◁ C
  ≡⟨⟩ 
    Γ ⧺ (Δ ⧺ Ξ) ◁ C
  ≡⟨⟩ 
    Γ ⧺ (Δ ⧺ Ξ ◁ C)
  ∎
 