{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_; _⊔_; lsuc)
open import Otus.Syntax.Typed.Base

open import Agda.Primitive using (Level; _⊔_; lsuc)

---- syntax

infix 3 intro 

intro : (Prop : Set) → Prop → Prop
intro _ proof = proof

syntax intro P proof = by-⟨ proof ⟩ P 

infix 3 begin_

begin_ : ∀ { P : Set } → P → P
begin_ proof = proof

infixl 2 step-∣  step-⟨⟩ 

step-∣ : (P : Set) → P → P
step-∣ _ proof = proof
step-⟨⟩ : { P : Set } (C : Set) → (P → C) → P → C
step-⟨⟩ _ rule = rule

syntax step-∣ P p           = p ⎯⎯⎯⎯ P
syntax step-⟨⟩ C r p        = p ⎯⎯⎯⎯⟨ r ⟩ C -- apply

infix 1 end-∎

end-∎ : {Jdg : Set} → Jdg → Jdg
end-∎ p = p

syntax end-∎ p = p ∎