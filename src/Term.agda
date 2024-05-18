module Term {name : Set} {exception : Set} where

open import Data.List
open import Util.Scope
open import Data.String

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  TRaise : (e : exception) → Term α
  TCatch : (e : exception) → (u v : Term α) → Term α
  TDecl  : (e : exception) → (u : Term α) → Term α
  