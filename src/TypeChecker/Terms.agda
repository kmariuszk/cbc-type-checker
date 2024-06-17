module TypeChecker.Terms {name : Set} where

open import TypeChecker.Types
open import Util.Scope
open import Data.List
open import Data.String

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ₛ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  TRaise : (e : String) → Term α
  TCatch : (e : String) → Term α → Term α → Term α
  TDecl  : (e : String) → Term α → Term α 
  -- Annotation type that is going to be used for lambdas (an equivalent of `_↓_ : Term⁻ → Type → Term⁺` term from PLFA)
  _↓_ : Term α → Type → Term α
  TIfThenElse : Term α → Term α → Term α → Term α
