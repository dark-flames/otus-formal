{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Properties.Utils.Context where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base
open import Otus.Syntax.Typed.Properties.Presuppositions


private
  variable
    Γ : Context
    A B : Term

{-
- Properties independent of context conversion
-}

--- Context

ctxExt : Γ ⊢ A → ⊢ Γ ▷ A
ctxExt Γ⊢A = CExt (tyWfCtx Γ⊢A) Γ⊢A

ctxEqExt₂ : ⊢ Γ → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ≡ⱼ B → ⊢ Γ ▷ A ≡ⱼ Γ ▷ B
ctxEqExt₂ ⊢Γ Γ⊢A Γ⊢B Γ⊢A≡B = CEqExt (CEqRefl ⊢Γ) Γ⊢A Γ⊢B Γ⊢A≡B