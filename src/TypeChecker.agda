module TypeChecker {name : Set} {exception : Set} where

open import Term {name}
open import TypeChecker.Type
open import TypeChecker.TypingRules {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope
open import Data.List

open import Agda.Builtin.Equality
open import Data.Product
open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name
  u : Term α

convert_list : (a b : List exception) → Evaluator (a ≡ b)
convert_list [] [] = return refl
-- TODO: add an actual comparison case
convert_list _ _ = evalError "unequal exceptions"

-- Type checking function application requires conversion checking,
-- i.e. checking whether two types are equal.
--
convert : (a b : Type) → Evaluator (a ≡ b)
convert nat nat = return refl
convert (la [ lφ ]⇒ lb) (ra [ rφ ]⇒ rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  refl ← convert_list lφ rφ
  return refl
convert _ _ = evalError "unequal types"

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Ξ : List exception) (Γ : Context Type α) u             (ann : Ann) → Evaluator (Σ[ t ∈ Type ] Ξ ◂ Γ ⊢ u ∶ t ∣ ann)
checkType : ∀ (Ξ : List exception) (Γ : Context Type α) u (ty : Type) (ann : Ann) → Evaluator (Ξ ◂ Γ ⊢ u ∶ ty ∣ ann)

-- synthesises
inferType eex ctx (TVar x index) exc = return (lookupVar ctx x index , TyTVar index)
inferType _ _ (TLam x body) _ = evalError "cannot infer the type of a lambda"
inferType eex ctx (TApp lam arg) exc = do
  -- does the first term of `TApp` has type of `_[_]⇒_`?
  (a [ φ ]⇒ b) , gtu ← inferType eex ctx lam exc
    where _ → evalError "application head should have a function type"
  gtv ← checkType eex ctx arg a φ
  return (b , TyTApp gtu gtv)
inferType _ _ _ _ = evalError "temporary error"

-- inherits
-- TODO: decide which other terms to add here (i.e., which terms are constructors and which are deconstructors)
checkType eex ctx (TLam x body) (a [ φ ]⇒ b) exc = do
  tr ← checkType eex (ctx , x ∶ a) body b φ
  return (TyTLam tr)
checkType _ _ (TLam x body) _ _ = evalError "lambda should have a function type"
checkType eex ctx term ty exc = do
  (t , tr) ← inferType eex ctx term exc
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr
 