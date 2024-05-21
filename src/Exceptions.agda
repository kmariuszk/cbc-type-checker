module Exceptions {name : Set} where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import Data.List
open import Util.Scope
open import Util.Context
open import Data.Empty
open import Data.String

-- We'll use annotated types, with annotations being a set of identifiers
-- marking the names of the kinds of exceptions that a computation might throw
Ann = List String

aempty : Ann
aempty = []

eempty : List String
eempty = []

{- Types with effect annotations (or, alternatively, where the function arrow is
   now a Kleisli morphism) -}
data Type : Set where
  nat    : Type
  _[_]⇒_ : (a : Type) → (φ : Ann) → (b : Type) → Type

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ₛ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  TRaise : (e : String) → Term α
  TCatch : (e : String) → Term α → Term α → Term α
  TDecl  : (e : String) → Term α → Term α 
  -- an equivalent of `_↓_ : Term⁻ → Type → Term⁺` term from PLFA
  -- Annotation type that is going to be used for lambdas
  _↓_ : Term α → Type → Term α

private variable
  x : name
  a b : Type
  u v : Term α
  φ φ₁ φ₂ : Ann
  Ξ : List String
  e : String

data _◂_⊢_∶_∣_ (Ξ : List String) (Γ : Context Type α) : Term α → Type → Ann → Set where

  TyTVar
    : (p : x ∈ₛ α)
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TVar x p ∶ lookupVar Γ x p ∣ φ

  TyTLam
    : Ξ ◂ (Γ , x ∶ a) ⊢ u ∶ b ∣ φ₁  
    -------------------------------------
    → Ξ ◂ Γ ⊢ TLam x u ∶ a [ φ₁ ]⇒ b ∣ φ₂

  TyTApp
    : Ξ ◂ Γ ⊢ u ∶ a [ φ ]⇒ b ∣ φ
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
    ----------------------------
    → Ξ ◂ Γ ⊢ TApp u v ∶ b ∣ φ

  TyTRaise
    : e ∈ Ξ
    → e ∈ φ
    --------------------------
    → Ξ ◂ Γ ⊢ TRaise e ∶ a ∣ φ 

  TyTCatch
    -- current term `TCatch` is annotated with exception `e`  
    : e ∉ φ
    -- when extended with term `u`, then it is annotated with exception `e`
    → Ξ ◂ Γ ⊢ u ∶ a ∣ (e ∷ φ)
    -- when extenteded with term `a`, then it is still not annotated with exception `e`
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
      ----------------------------
    → Ξ ◂ Γ ⊢ TCatch e u v ∶ a ∣ φ

  TyTDecl
    : (e ∷ Ξ) ◂ Γ ⊢ u ∶ a ∣ φ
    ---------------------------
    → Ξ ◂ Γ ⊢ TDecl e u ∶ a ∣ φ 

  TyTAnn
    : Ξ ◂ Γ ⊢ u ∶ a ∣ φ
    → Ξ ◂ Γ ⊢ (u ↓ a) ∶ a ∣ φ
