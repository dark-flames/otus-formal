module Otus.Definition.Untyped.Context where

open import Otus.Definition.Untyped.Term

infixl 30 _,_

data Context : Set where
    ε : Context
    _,_ : Context → Term → Context