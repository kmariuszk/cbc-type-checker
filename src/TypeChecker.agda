module TypeChecker {name : Set} where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import Data.String
open import Exceptions {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope
open import Relation.Nullary

open import Agda.Builtin.Equality
open import Data.Product
open import Data.List
open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name
  u : Term α

convert_list : (a b : List String) → Evaluator (a ≡ b)
convert_list [] [] = return refl
convert_list (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes refl = do
  refl <- convert_list xs ys
  return refl
... | no _ = evalError "unequal exceptions"
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
inferType : ∀ (Ξ : List String) (Γ : Context Type α) u             (ann : Ann) → Evaluator (Σ[ t ∈ Type ] Ξ ◂ Γ ⊢ u ∶ t ∣ ann)
checkType : ∀ (Ξ : List String) (Γ : Context Type α) u (ty : Type) (ann : Ann) → Evaluator (Ξ ◂ Γ ⊢ u ∶ ty ∣ ann)

inferType Ξ ctx (TVar x index) exc = return (lookupVar ctx x index , TyTVar index)
inferType Ξ ctx (TLam x body) exc = evalError "cannot infer the type of a lambda"
inferType Ξ ctx (TRaise e) exc = evalError "cannot infer the type of a raising error"
inferType Ξ ctx (TCatch e teTerm faTerm) exc = evalError "cannot infer the type of catching block"
inferType Ξ ctx (TDecl e term) exc = evalError "cannot infer the type of an exception declaration"
inferType Ξ ctx (TApp lam arg) exc = do
  (a [ φ ]⇒ b) , gtu ← inferType Ξ ctx lam exc
    where _ → evalError "application head should have a function type"
  refl ← convert_list φ exc
  gtv ← checkType Ξ ctx arg a exc
  return (b , TyTApp gtu gtv)
inferType Ξ ctx (term ↓ type) exc = do
  tr ← checkType Ξ ctx term type exc
  return (type , TyTAnn tr)
  
checkType Ξ ctx (TLam x body) (a [ φ ]⇒ b) exc = do
  tr ← checkType Ξ (ctx , x ∶ a) body b φ
  return (TyTLam tr)
checkType _ _ (TLam _ _) _ _ = evalError "lambda should have a function type"
checkType Ξ ctx (TDecl e term) ty exc = do
  tr ← checkType (e ∷ Ξ) ctx term ty exc
  return (TyTDecl tr)
checkType Ξ ctx (TRaise e) ty exc with e ∈? Ξ | e ∈? exc
...                             | yes (e∈Ξ)   | yes (e∈exc) = return (TyTRaise e∈Ξ e∈exc)
...                             | _           | _           = evalError "raising an exception that has not been declared"
checkType Ξ ctx (TCatch e teTerm faTerm) ty exc with e ∉? exc
...                             | yes e∉exc                 = do
  tr₁ ← checkType Ξ ctx teTerm ty (e ∷ exc)
  tr₂ ← checkType Ξ ctx faTerm ty exc
  return (TyTCatch e∉exc tr₁ tr₂)
...                             | no _                      = evalError "checking an exception that's already covered"
checkType Ξ ctx term ty exc = do
  (t , tr) ← inferType Ξ ctx term exc
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr
