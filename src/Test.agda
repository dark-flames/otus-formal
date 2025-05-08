module Test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

test : { B C : Set }→ B ≡ C → Set
test refl = {!   !}
