{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Inversion.Type where

open import Otus.Utils
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Stability
open import Otus.Syntax.Typed.Presupposition.WfCtx
open import Otus.Syntax.Typed.Presupposition.Utils
open import Otus.Syntax.Typed.Presupposition.Inversion.Base
open import Otus.Syntax.Typed.Presupposition.Inversion.Term

open Product

private
  variable
    Γ : Context
    A B : Term

piTyInversion : Γ ⊢ Pi A B → Γ ⊢ A × Γ ◁ A ⊢ B
piTyInversion (tyJdg u Γ⊢PiAB∈u) = piTmInversion Γ⊢PiAB∈u



   