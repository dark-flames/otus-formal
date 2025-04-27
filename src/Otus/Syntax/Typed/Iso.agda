{-# OPTIONS --without-K --safe #-}

module Otus.Syntax.Typed.Iso where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)

private
  variable
    Γ Δ Ξ : Context
    A a : Term

record _≃ᶜ_ (Γ Δ : Context) :  Set where
  constructor CtxIso
  field
    domain : ⊢ Γ
    codomain : ⊢ Δ
    to : Substitution
    from : Substitution
    toWf : Γ ⊢ to ⇒ Δ
    fromWf : Δ ⊢ from ⇒ Γ
    from∘to : Γ ⊢ from ∘ to ≡ⱼ idₛ ⇒ Γ
    to∘from : Δ ⊢ to ∘ from ≡ⱼ idₛ ⇒ Δ
open _≃ᶜ_

≃ᶜ-refl : ⊢ Γ → Γ ≃ᶜ Γ
≃ᶜ-refl wf = let wfId = SbId wf
  in let compEq = SbEqIdₗ  wfId wfId
  in record {
    domain = wf ;
    codomain = wf ;
    to = idₛ ;
    from = idₛ ;
    toWf = wfId ;
    fromWf = wfId ;
    from∘to = compEq ;
    to∘from = compEq
  }

≃ᶜ-sym : Γ ≃ᶜ Δ → Δ ≃ᶜ Γ
≃ᶜ-sym (CtxIso codomain' domain' from' to' fromWf' toWf' to∘from' from∘to') =
  record {
    domain = domain' ;
    codomain = codomain' ;
    to = to' ;
    from = from' ;
    toWf = toWf' ;
    fromWf = fromWf' ;
    from∘to = from∘to' ;
    to∘from = to∘from'
  }

open Subst-≡ⱼ-Comp
≃ᶜ-trans : Δ ≃ᶜ Ξ → Γ ≃ᶜ Δ → Γ ≃ᶜ Ξ
≃ᶜ-trans (CtxIso domain₁ codomain₁ to₁ from₁ toWf₁ fromWf₁ from∘to₁ to∘from₁)
         (CtxIso domain₂ codomain₂ to₂ from₂ toWf₂ fromWf₂ from∘to₂ to∘from₂) 
    = let toWf' = SbComp toWf₁ toWf₂
      in let fromWf' = SbComp fromWf₂ fromWf₁
      in record {
          domain = domain₂;
          codomain = codomain₁ ;
          to = to₁ ∘ to₂ ;
          from = from₂ ∘ from₁ ;
          toWf = toWf' ;
          fromWf = fromWf';
      ---- from₂ ∘ from₁ ∘ (to₁ ∘ to₂)
          from∘to = ---- from₂ ∘ from₁ ∘ (to₁ ∘ to₂)
              SbEqCompAssoc fromWf₂ fromWf₁ toWf'
            ⟨⟩ ---- =>  from₂ ∘ (from₁ ∘ (to₁ ∘ to₂))
              SbEqComp (SbEqRefl fromWf₂) (
                  ---- => from₂ ∘ (from₁ ∘ to₁ ∘ to₂)
                  SbEqSym (SbEqCompAssoc fromWf₁ toWf₁ toWf₂)
                ⟨⟩ ---- => from₂ ∘ (idₛ ∘ to₂)
                  SbEqComp from∘to₁ (SbEqRefl toWf₂)
                ⟨⟩ ---- => from₂ ∘ to₂
                  SbEqIdₗ (SbId domain₁) toWf₂
              )
            ⟨⟩ ---- => idₛ
              from∘to₂

            ;

          to∘from = ---- to₁ ∘ to₂ ∘ (from₂ ∘ from₁)
              SbEqCompAssoc toWf₁ toWf₂ fromWf'
            ⟨⟩ ---- => to₁ ∘ (to₂ ∘ (from₂ ∘ from₁))
              SbEqComp (SbEqRefl toWf₁) (
                  ---- => to₁ ∘ (to₂ ∘ from₂ ∘ from₁)
                  SbEqSym (SbEqCompAssoc toWf₂ fromWf₂ fromWf₁ )
                ⟨⟩ ---- => to₁ ∘ (idₛ ∘ from₁)
                  SbEqComp to∘from₂ (SbEqRefl fromWf₁)
                ⟨⟩ ---- => to₁ ∘ from₁
                  SbEqIdₗ (SbId domain₁) fromWf₁
              )
            ⟨⟩ ---- => idₛ
              to∘from₁
        }



postulate
  ≃ᶜ-extₗ : (iso : Γ ≃ᶜ Δ) → Γ ⊢ A → Γ , A ≃ᶜ Δ , (A [ to iso ]ₑ)
  ≃ᶜ-extᵣ : (iso : Γ ≃ᶜ Δ) → Δ ⊢ A → Γ , (A [ from iso ]ₑ) ≃ᶜ Δ , A
  ≃ᶜ-refl-ext : ⊢ Γ → Γ ⊢ A ≡ⱼ B → Γ , A ≃ᶜ Γ , B

 