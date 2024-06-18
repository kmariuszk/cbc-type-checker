module TypeChecker.Types where

open import Util.Annotation

data Type : Set where
  nat    : Type
  bool : Type
  _[_]⇒_ : (a : Type) → (φ : Ann) → (b : Type) → Type
