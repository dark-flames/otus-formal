{-# OPTIONS --without-K #-}
module Otus.Syntax.Typed.Properties.EqPresuppositions where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions
open import Otus.Syntax.Typed.Properties.ContextConversion

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; J)
open import Data.Product renaming (_,_ to pair)
open import Function.Base using (id)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Γ' Δ Ξ Θ  : Context
    γ γ₁ γ₂ δ δ₁ δ₂ : Substitution
    f a b c A B C T : Term
open _⊢_⇒_
open ⊢_
open _⊢_

postulate
    tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢ B
    
    tmEqWf : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ a ∷ A × Γ ⊢ b ∷ A

substEqWf : Γ ⊢ γ₁ ≡ⱼ γ₂ ⇒ Δ → Γ ⊢ γ₁ ⇒ Δ × Γ ⊢ γ₂ ⇒ Δ

substEqWf {Γ}{γ₁} {γ₂} {Δ} sb with sb
... | SbEqRefl Γ⇒Δ = pair Γ⇒Δ Γ⇒Δ
... | SbEqSym Γ⊢γ₂≡ⱼγ₁⇒Δ = swap (substEqWf Γ⊢γ₂≡ⱼγ₁⇒Δ)
... | SbEqTrans Γ⊢γ₁≡ⱼγ₂⇒Δ Γ⊢γ₂≡ⱼγ₃⇒Δ  = pair (proj₁ (substEqWf Γ⊢γ₁≡ⱼγ₂⇒Δ)) (proj₂ (substEqWf Γ⊢γ₂≡ⱼγ₃⇒Δ))
... | SbEqExt Γ⊢γ₁≡ⱼγ₂⇒Δ Δ⊢A Γ⊢a≡b∷Aγ₁ = let Γ⊢Aγ₁≡Aγ₂ = TyEqSubst (TyEqRefl Δ⊢A) Γ⊢γ₁≡ⱼγ₂⇒Δ
    in let pair Γ⊢γ₁⇒Δ Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡ⱼγ₂⇒Δ
    in let pair Γ⊢a∷Aγ₁ Γ⊢b∷Aγ₁ = tmEqWf Γ⊢a≡b∷Aγ₁
    in let Γ⊢b∷Aγ₂ = TmTyConv Γ⊢b∷Aγ₁ Γ⊢Aγ₁≡Aγ₂
    in pair (SbExt Γ⊢γ₁⇒Δ Δ⊢A Γ⊢a∷Aγ₁) (SbExt Γ⊢γ₂⇒Δ Δ⊢A Γ⊢b∷Aγ₂)
... | SbEqComp Δ⊢δ₁≡δ₂⇒Ξ Γ⊢γ₁≡γ₂⇒Δ = let pair Δ⊢δ₁⇒Ξ Δ⊢δ₂⇒Ξ = substEqWf Δ⊢δ₁≡δ₂⇒Ξ
    in let pair Γ⊢γ₁⇒Δ Γ⊢γ₂⇒Δ = substEqWf Γ⊢γ₁≡γ₂⇒Δ
    in pair (SbComp Δ⊢δ₁⇒Ξ Γ⊢γ₁⇒Δ) (SbComp Δ⊢δ₂⇒Ξ Γ⊢γ₂⇒Δ)
... | SbEqConv Γ⊢γ₁≡ⱼγ₂⇒Δ₁ ⊢Δ₁≡Δ₂ = let pair Γ⊢γ₁⇒Δ₁ Γ⊢γ₂⇒Δ₁ = substEqWf Γ⊢γ₁≡ⱼγ₂⇒Δ₁
    in pair (SbConv Γ⊢γ₁⇒Δ₁ ⊢Δ₁≡Δ₂) (SbConv Γ⊢γ₂⇒Δ₁ ⊢Δ₁≡Δ₂)
... | SbEqCompAssoc Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ Γ⊢γ⇒Δ = let Γ⊢ξ∘δ∘γ⇒Θ = SbComp (SbComp Ξ⊢ξ⇒Θ Δ⊢δ⇒Ξ) Γ⊢γ⇒Δ
    in let Γ⊢ξ∘[δ∘γ]⇒Θ = SbComp Ξ⊢ξ⇒Θ  (SbComp Δ⊢δ⇒Ξ Γ⊢γ⇒Δ)
    in pair Γ⊢ξ∘δ∘γ⇒Θ Γ⊢ξ∘[δ∘γ]⇒Θ
... | SbEqIdₗ Δ⊢id⇒Ξ Γ⊢γ⇒Δ = ?
