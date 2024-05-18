module TypeChecker.TypingRules {name : Set} {exception : Set} where

open import Data.List
open import Data.Empty
open import Term {name}
open import TypeChecker.Type
open import Util.Context {name}
open import Util.Scope

private variable
  x : name
  α : Scope name
  a b : Type
  u v : Term α
  φ φ₁ φ₂ : Ann
  Ξ : List exception
  e : exception

-- Context contains names with types
data _◂_⊢_∶_∣_ (Ξ : List exception) (Γ : Context Type α) : Term α → Type → Ann → Set where
  TyTVar
    : (p : x ∈ α)
    -------------------------------
    → Ξ ◂ Γ ⊢ TVar x p ∶ lookupVar Γ x p ∣ φ

  TyTLam
    : Ξ ◂ (Γ , x ∶ a) ⊢ u ∶ b ∣ φ₁
    -------------------------------
    → Ξ ◂ Γ ⊢ TLam x u ∶ a [ φ₁ ]⇒ b ∣ φ₂

  TyTApp
    -- There's a term `u` of type `a [ φ ]⇒ b`, where all the possible exceptions that could be thrown are `φ`
    : Ξ ◂ Γ ⊢ u ∶ a [ φ ]⇒ b ∣ φ

    -- There's a term `v` of type `a`, where all the possible exceptions that could be thrown are `φ`
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
    -------------------------------
    → Ξ ◂ Γ ⊢ TApp u v ∶ b ∣ φ

  TyTRaise
    : e ∈ Ξ
    → e ∈ φ
    -------------------------------
    → Ξ ◂ Γ ⊢ TRaise e ∶ a ∣ φ 

  TyTCatch
    : e ∈ φ → ⊥
    → Ξ ◂ Γ ⊢ u ∶ a ∣ (e ∷ φ)
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
    -------------------------------
    → Ξ ◂ Γ ⊢ TCatch e u v ∶ a ∣ φ

  TyTDecl
    : (e ∷ Ξ) ◂ Γ ⊢ u ∶ a ∣ φ
    ---------------------------
    → Ξ ◂ Γ ⊢ TDecl e u ∶ a ∣ φ 

infix 3 _◂_⊢_∶_∣_
 