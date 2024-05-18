module TypeChecker.Type {exception : Set} where

open import Data.List

-- We'll use annotated types, with annotations being a set of identifiers
-- marking the names of the kinds of exceptions that a computation might throw
Ann = List exception

data Type : Set where
  nat    : Type
  _[_]⇒_ : (a : Type) → (φ : Ann) → (b : Type) → Type
