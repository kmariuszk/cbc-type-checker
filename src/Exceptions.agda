module Exceptions {name : Set} where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import Data.List
open import Util.Scope
open import Util.Context
open import Util.Annotation
open import Data.Empty
open import Data.String hiding (_++_)

{- Types with effect annotations (or, alternatively, where the function arrow is
   now a Kleisli morphism) -}
data Type : Set where
  nat    : Type
  bool : Type
  unit : Type
  _[_]⇒_ : (a : Type) → (φ : Ann) → (b : Type) → Type


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
  TIfThenElse : Term α → Term α → Term α → Term α

private variable
  α : Scope name
  x : name
  a b : Type
  cond u v : Term α
  φ φ₁ φ₂ φ₃ φ₄ φ₅ : Ann
  Ξ : List String
  e : String

infix 20 _◂_⊢_∶_∣_  

data _◂_⊢_∶_∣_ (Ξ : List String) (Γ : Context Type α) : Term α → Type → Ann → Set where

  TyTVar
    : (p : x ∈ₛ α)
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TVar x p ∶ lookupVar Γ x p ∣ φ

  TyTLam
    : Ξ ◂ (Γ , x ∶ a) ⊢ u ∶ b ∣ φ₃ 
    → φ₁ ∪ φ₂ ≡ φ₃ 
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TLam x u ∶ a [ φ₁ ]⇒ b ∣ φ₂
  
  TyTApp
    : Ξ ◂ Γ ⊢ u ∶ a [ φ₁ ]⇒ b ∣ φ₂
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ₃
    → φ₁ ∪ φ₂ ≡ φ₄
    → φ₃ ∪ φ₄ ≡ φ₅
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TApp u v ∶ b ∣ φ₅

  TyTRaise
    : e ∈ Ξ
    → e ∈ₐ φ
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TRaise e ∶ a ∣ φ 

  TyTCatch
    : Ξ ◂ Γ ⊢ u ∶ a ∣ (φ₁ +++ e)
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ₂
    → φ₁ ∪ φ₂ ≡ φ₃
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TCatch e u v ∶ a ∣ φ₃

  TyTDecl
    : (e ∷ Ξ) ◂ Γ ⊢ u ∶ a ∣ φ
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TDecl e u ∶ a ∣ φ 

  TyTAnn
    : Ξ ◂ Γ ⊢ u ∶ a ∣ φ
    ----------------------------------------
    → Ξ ◂ Γ ⊢ (u ↓ a) ∶ a ∣ φ

  TyTIfThenElse
    : Ξ ◂ Γ ⊢ cond ∶ bool ∣ φ₁
    → Ξ ◂ Γ ⊢ u ∶ a ∣ φ₂
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ₃
    → φ₁ ∪ φ₂ ≡ φ₄
    → φ₃ ∪ φ₄ ≡ φ₅
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TIfThenElse cond u v ∶ a ∣ φ₅ 