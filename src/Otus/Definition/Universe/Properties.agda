module Otus.Definition.Universe.Properties where

open import Otus.Definition.Universe.Base
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality hiding (cong)

cong : ∀ {l₁ l₂} → l₁ ≡ l₂ → lsuc l₁ ≡ lsuc l₂
cong refl = refl

⊔-identity : ∀ {l} → l ⊔ l ≡ l
⊔-identity {lzero} = refl
⊔-identity {lsuc l} = cong (⊔-identity)

⊔-lzeroʳ : ∀ {l} → l ⊔ lzero ≡ l
⊔-lzeroʳ {lzero} = refl
⊔-lzeroʳ {lsuc l} = refl

⊔-comm : ∀ {l₁ l₂} → l₁ ⊔ l₂ ≡ l₂ ⊔ l₁
⊔-comm {lzero} {l₂} = sym ⊔-lzeroʳ
⊔-comm {lsuc l₁} {lzero} = refl
⊔-comm {lsuc l₁} {lsuc l₂} = cong ( ⊔-comm {l₁} {l₂} )

⊔-assoc : ∀ {l₁ l₂ l₃} → (l₁ ⊔ l₂) ⊔ l₃ ≡ l₁ ⊔ (l₂ ⊔ l₃)
⊔-assoc {lzero} {l₂} {l₃} = refl
⊔-assoc {lsuc l₁} {lzero} {l₃} = refl
⊔-assoc {lsuc l₁} {lsuc l₂} {lzero} = refl
⊔-assoc {lsuc l₁} {lsuc l₂} {lsuc l₃} = cong (⊔-assoc {l₁} {l₂} {l₃})