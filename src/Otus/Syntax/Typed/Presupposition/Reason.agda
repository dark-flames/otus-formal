{-# OPTIONS --without-K --safe #-}
module Otus.Syntax.Typed.Presupposition.Reason where

open import Otus.Syntax.Typed.Reason.Base public
open import Otus.Syntax.Typed.Presupposition.Reason.Subst public
open import Otus.Syntax.Typed.Presupposition.Reason.Term public

open import Otus.Syntax.Typed.Presupposition.Base
open import Otus.Syntax.Typed.Presupposition.Relation

import Otus.Syntax.Typed.Reason.Eq as REq

module TyEqReason = REq.TyEqReason _⊢_≡ⱼ_ tyEqSym tyEqTrans
module TmEqReason = REq.TmEqReason _⊢_≡ⱼ_∷_ TmEqSym TmEqTrans