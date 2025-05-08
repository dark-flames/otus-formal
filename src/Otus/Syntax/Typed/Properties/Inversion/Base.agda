{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Inversion.Base where

open import Otus.Syntax.Untyped hiding (_∘_)
open import Otus.Syntax.Typed.Base

open import Data.Product renaming (_,_ to pair)

private
  variable
    l : ULevel
    Γ Δ  : Context
    a A B : Term
    γ : Substitution

ctxEqInversion : ⊢ Γ ≡ⱼ Δ → Context × Context
ctxEqInversion { Γ } { Δ } _ = pair Γ Δ

ctxExtInversion : ⊢ Γ , A → ⊢ Γ × Γ ⊢ A
ctxExtInversion (CExt ⊢Γ Γ⊢A) = pair ⊢Γ Γ⊢A

tyInversion : Γ ⊢ A → Context × Term
tyInversion { Γ } { A } _ = pair Γ A

tyEqInversion : Γ ⊢ A ≡ⱼ B → Context × Term × Term
tyEqInversion { Γ } { A } { B } _ = pair Γ (pair A B)

substInversion : Γ ⊢ γ ⇒ Δ → Context × Substitution × Context
substInversion { Γ } { γ } { Δ } Γ⊢γ⇒Δ = pair Γ (pair γ Δ)

tmInversion : Γ ⊢ a ∷ A → Context × Term × Term
tmInversion { Γ } { a } { A } _ = pair Γ (pair a A)

univInversion : Γ ⊢ A ∷ U l → ULevel
univInversion {_} {_} {l} _ = l