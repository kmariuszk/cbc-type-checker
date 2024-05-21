module Util.Scope where

open import Data.List

-- Scope is defined as a list of names.
--
Scope : (name : Set) → Set
Scope name = List name

-- An assertion for "x is a member of the scope".
-- With a custom name, so it doesn't clash with the `∈` definition for lists
data _∈ₛ_ {name : Set} (x : name) : Scope name → Set where
    hereₛ  : ∀ {ns : Scope name}                          → x ∈ₛ (x ∷ ns)
    thereₛ : ∀ {n : name} {ns : Scope name} (_ : x ∈ₛ ns) → x ∈ₛ (n ∷ ns)

sempty : {name : Set} → Scope name
sempty = []
