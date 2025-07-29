{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Utils.Context where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Relation


private
  variable
    Γ : Context
    A B : Term

{-
- Properties independent of context conversion
-}

--- Context

ctxExt : Γ ⊢ A → ⊢ Γ ◁ A
ctxExt Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A

ctxEqExt₂ : ⊢ Γ → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B → ⊢ Γ ◁ A ≡ⱼ Γ ◁ B
ctxEqExt₂ ⊢Γ Γ⊢A Γ⊢B Γ⊢A≡B = CEqExt (ctxEqRefl ⊢Γ) Γ⊢A Γ⊢B Γ⊢A≡B Γ⊢A Γ⊢B Γ⊢A≡B 