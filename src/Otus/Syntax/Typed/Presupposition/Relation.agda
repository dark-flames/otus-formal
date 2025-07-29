{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Relation where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Univ


private
  variable
    Γ Δ Ξ : Context
    γ δ : Substitution
    A B C : Type
    a b  : Term


tmEqRefl : Γ ⊢ a ∷ A → Γ ⊢ a ≡ⱼ a ∷ A
tmEqRefl Γ⊢a∷A = let
    Γ⊢a[idₛ]ₑ≡a∷A = TmEqSubstId Γ⊢a∷A
  in TmEqTrans (TmEqSym Γ⊢a[idₛ]ₑ≡a∷A) Γ⊢a[idₛ]ₑ≡a∷A

sbEqRefl : Γ ⊢ γ ⇒ Δ → Γ ⊢ γ ≡ⱼ γ ⇒ Δ
sbEqRefl Γ⊢γ⇒Δ = let
    ⊢Γ = sbWfCtx Γ⊢γ⇒Δ
    Γ⊢γ∘idₛ≡γ⇒Δ = SbEqIdᵣ Γ⊢γ⇒Δ (SbId ⊢Γ)
  in SbEqTrans (SbEqSym Γ⊢γ∘idₛ≡γ⇒Δ) Γ⊢γ∘idₛ≡γ⇒Δ

tyEqRefl : Γ ⊢ A → Γ ⊢ A ≡ⱼ A
tyEqRefl (tyJdg u Γ⊢A∷Ul) = tyEqJdg u (tmEqRefl Γ⊢A∷Ul)

tyEqSym : Γ ⊢ A ≡ⱼ B → Γ ⊢ B ≡ⱼ A
tyEqSym (tyEqJdg u Γ⊢A≡B∷Ul) = tyEqJdg u (TmEqSym Γ⊢A≡B∷Ul)

tyEqTrans : Γ ⊢ A ≡ⱼ B → Γ ⊢ B ≡ⱼ C
  → Γ ⊢ A ≡ⱼ C
tyEqTrans (tyEqJdg u₁ Γ⊢A≡B∈u₁) (tyEqJdg u₂ Γ⊢B≡C∈u₂) = let
    Γ⊢A≡B∈u₁⊔u₂ = liftTyEq Γ⊢A≡B∈u₁ u₁⊆u₁⊔u₂
    Γ⊢B≡C∈u₁⊔u₂ = liftTyEq Γ⊢B≡C∈u₂ u₂⊆u₁⊔u₂
    Γ⊢A≡C∈u₁⊔u₂ = TmEqTrans Γ⊢A≡B∈u₁⊔u₂ Γ⊢B≡C∈u₁⊔u₂
  in tyEqJdg (u₁ ⊔ᵤ u₂) Γ⊢A≡C∈u₁⊔u₂


ctxEqExtRefl : ⊢ Γ ≡ⱼ Δ → Γ ⊢ A → Δ ⊢ A → ⊢ Γ ◁ A ≡ⱼ Δ ◁ A
ctxEqExtRefl ⊢Γ≡Δ Γ⊢A Δ⊢A = CEqExt ⊢Γ≡Δ Γ⊢A Γ⊢A (tyEqRefl Γ⊢A) Δ⊢A Δ⊢A (tyEqRefl Δ⊢A)

ctxEqRefl : ⊢ Γ → ⊢ Γ ≡ⱼ Γ
ctxEqRefl CEmp = CEqEmp
ctxEqRefl (CExt ⊢Γ Γ⊢A) = let ⊢Γ≡Γ = ctxEqRefl ⊢Γ
  in ctxEqExtRefl ⊢Γ≡Γ Γ⊢A Γ⊢A

ctxEqSym : ⊢ Γ ≡ⱼ Δ → ⊢ Δ ≡ⱼ Γ
ctxEqSym eq with eq
...| CEqEmp = CEqEmp
...| CEqExt ⊢Γ≡ⱼΔ Γ⊢A Γ⊢B Γ⊢A≡B Δ⊢A Δ⊢B Δ⊢A≡B = 
  CEqExt (ctxEqSym ⊢Γ≡ⱼΔ) Δ⊢B Δ⊢A (tyEqSym Δ⊢A≡B) Γ⊢B Γ⊢A (tyEqSym Γ⊢A≡B)