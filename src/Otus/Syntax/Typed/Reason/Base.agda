{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Reason.Base where

open import Otus.Utils
open import Otus.Syntax.Untyped hiding (_∘_; _⊔_; lsuc; lzero)
open import Otus.Syntax.Typed.Base

open import Agda.Primitive using (Level; _⊔_; lsuc ; lzero)



---- intro

record PremiseExt { l₁ l₂ }
    (Premise : Set l₁ → Set (l₁ ⊔ l₂))
    (PreProp : Set l₁) : Set (lsuc (l₁ ⊔ l₂)) where
  field
    append-proved : (premise : Premise PreProp) → (ExtProp : Set l₁) → ExtProp → Premise (PreProp × ExtProp)

open PremiseExt {{...}} public

record ProvedPremise {l} (Prop : Set l) : Set l where
  field
    proof : Prop

record PremiseWithHole { l₁ l₂ } (Hole : Set l₁) (Prop : Set l₂)  : Set (l₁ ⊔ l₂) where
  field
    proofConstr : Hole → Prop

instance 
  provedPremiseExt : ∀ {l} { PreProp : Set l } 
      → PremiseExt {l} {l} (ProvedPremise) PreProp
  append-proved {{provedPremiseExt}} premise _ proof = record { proof = (ProvedPremise.proof premise) , proof }

  premiseWithHoleExt : ∀ {l₁ l₂} { PreProp : Set l₁} { Hole : Set l₂} 
      → PremiseExt {l₁} {l₂}  (PremiseWithHole Hole) PreProp
  append-proved {{premiseWithHoleExt}} premise _ proof = record {
      proofConstr = λ { p → (PremiseWithHole.proofConstr premise) p , proof }
    }

append-hole : ∀ { PreProp : Set } 
    → ProvedPremise PreProp → (Hole : Set) 
    → PremiseWithHole Hole (PreProp × Hole) 
append-hole premise _ = record {
    proofConstr = λ { p → (ProvedPremise.proof premise) , p }
  }


infix 5 intro
infixl 4 ∧-intro ∧-derive

intro : (Prop : Set) → Prop → ProvedPremise Prop
intro _ proof = record { proof = proof }

∧-intro = append-proved
∧-derive = append-hole

syntax intro P proof = intro-⟨ proof ⟩ P 
syntax ∧-intro pre P proof = pre ∧-intro-⟨ proof ⟩ P 
syntax ∧-derive pre P proof = pre ∧-derive-⟨ proof ⟩ P

---- begin syntax

infix 3 begin_

begin_ : ∀ { Prop : Set } → ProvedPremise Prop → Prop
begin_ proof = ProvedPremise.proof proof


---- inference step

infixl 2 step-∣  step-⟨⟩ step-⟨⟩-with

step-∣ : (Prop : Set) → ProvedPremise Prop → ProvedPremise Prop
step-∣ _ proof = proof

step-⟨⟩ : ∀ { Prop : Set } (Conc : Set) → (Prop → Conc) → Prop → Conc
step-⟨⟩ _ rule = rule

step-⟨⟩-with : ∀ { Prop Conc Hole : Set } 
    → (Prop → Hole) → Prop → PremiseWithHole Hole Conc 
    → Conc
step-⟨⟩-with rule p c = (PremiseWithHole.proofConstr c) (rule p)

syntax step-∣ P p           = p ⎯⎯⎯⎯ P
syntax step-⟨⟩ C r p        = p ⎯⎯⎯⎯⟨ r ⟩ C -- apply
syntax step-⟨⟩-with r p C        = p ⎯⎯⎯⎯⟨ r ⟩-with C -- apply


---- end syntax
infix 1 end-∎

end-∎ : {Jdg : Set} → Jdg → Jdg
end-∎ p = p

syntax end-∎ p = p ∎