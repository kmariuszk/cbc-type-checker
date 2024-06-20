module TypeChecker {name : Set} where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import TypeChecker.Terms {name}
open import TypeChecker.Types
open import TypeChecker.TypingRules
open import Data.String hiding (_++_)
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope
open import Util.Annotation
open import Relation.Nullary
open import Function using (case_of_; _$_)

open import Agda.Builtin.Equality
open import Data.Product
open import Data.List
open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name

-- Checking whether two annotations are equal.
convertAnn : (a b : Ann) → Evaluator (a ≡ b)
convertAnn ∅ ∅ = return refl
convertAnn (s₁ +++ φ₁) (s₂ +++ φ₂) with s₁ ≟ s₂
... | yes refl = do
  refl <- convertAnn φ₁ φ₂
  return refl
... | no _ = evalError "Unequal exceptions when converting annotations!"
convertAnn _ _ = evalError "Unequal exceptions when converting annotations!"

-- Checking whether two types are equal.
convert : (a b : Type) → Evaluator (a ≡ b)
convert nat nat = return refl
convert bool bool = return refl
convert (la [ lφ ]⇒ lb) (ra [ rφ ]⇒ rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  refl ← convertAnn lφ rφ
  return refl
convert _ _ = evalError "Unequal types when converting types!" 

helperFunctionOne : (e : String) → (φ : Ann) → Evaluator (e ∈ₐ φ)
helperFunctionOne e φ with e ∈ₐ? φ
... | yes e∈φ = return e∈φ
... | no _ = evalError "Catching not an annotated exception!"

helperFunctionTwo : (e : String) → (φ : Ann) → Evaluator (¬ (e ∈ₐ φ))
helperFunctionTwo e φ with e ∈ₐ? φ
... | yes _ = evalError "Handle-branch of TCatch should not contain the exception!"
... | no e∉φ = return e∉φ

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Ξ : List String) (Γ : Context Type α) u             → Evaluator (Σ[ t ∈ Type ] Σ[ φ ∈ Ann ] Ξ ◂ Γ ⊢ u ∶ t ∣ φ)
checkType : ∀ (Ξ : List String) (Γ : Context Type α) u (ty : Type) → Evaluator (Σ[ φ ∈ Ann ] Ξ ◂ Γ ⊢ u ∶ ty ∣ φ)

inferType Ξ Γ (TVar x index)              = return (lookupVar Γ x index , (∅ , TyTVar index))
inferType Ξ Γ (TLam x body)               = evalError "Type-checker cannot infer the type of a lambda!"
inferType Ξ Γ (TRaise e)                  = evalError "Type-checker cannot infer the type of a raising error!"
inferType Ξ Γ (TCatch e teTerm faTerm)    = evalError "Type-checker cannot infer the type of a catching block!"
inferType Ξ Γ (TDecl e term)              = evalError "Type-checker cannot infer the type of an exception declaration!"
inferType Ξ Γ (TIfThenElse e tTerm eTerm) = evalError "Type-checker cannot infer the type of an if-statement declaration!"
inferType Ξ Γ (TApp lam arg)              = do
  -- Infer types for the head and argument of the application.
  (a [ φ₁ ]⇒ b , (φ₂ , tr₁)) ← inferType Ξ Γ lam
    where _ → evalError "Application head should have a function type!"
  (φ₃ , tr₂) ← checkType Ξ Γ arg a

  -- Sum the annotations of the head and argument.
  let (φ₄ , φ₄-proof) = mergeAnn φ₁ φ₂
      (φ₅ , φ₅-proof) = mergeAnn φ₃ φ₄

  return (b , (φ₅ , TyTApp tr₁ tr₂ φ₄-proof φ₅-proof))
inferType Ξ Γ (term ↓ type)                = do
  (φ , tr) ← checkType Ξ Γ term type
  return (type , (φ , TyTAnn tr))

checkType Ξ Γ (TLam x body) (a [ φ₁ ]⇒ b) = do
  -- Check the type of the body of the lambda.
  (φ₂ , tr) ← checkType Ξ (Γ , x ∶ a) body b

  -- Ensure φ₁ is equal to φ₂.
  refl ← convertAnn φ₁ φ₂
  
  return (∅ , TyTLam tr)
checkType _ _ (TLam _ _) _ = evalError "Lambda should have a function type!"
checkType Ξ Γ (TDecl e term) ty            = do
  (φ , tr) ← checkType (e ∷ Ξ) Γ term ty
  return (φ , TyTDecl tr)
checkType Ξ Γ (TRaise e) ty with e ∈? Ξ
...                             | yes (e∈Ξ)  = return (e +++ ∅ , TyTRaise e∈Ξ)
...                             | no _       = evalError "Raising a not declared exception!"
checkType Ξ Γ (TCatch e exceptionTerm handleTerm) ty with e ∈? Ξ
...                             | no _ = evalError "Catching a not declared exception!"
...                             | yes (e∈Ξ) = do
  -- Check types for the exception term and the exception handler.
  (φ₁ , tr₁) ← checkType Ξ Γ exceptionTerm ty
  (φ₂ , tr₂) ← checkType Ξ Γ handleTerm ty

  -- Calculate the subtraction.
  let (φ₃ , φ₃-proof) = removeAnn φ₁ e

  -- Calculate the sum of terms.
  let (φ₄ , φ₄-proof) = mergeAnn φ₃ φ₂

  e∈φ₁ ← helperFunctionOne e φ₁
  e∉φ₂ ← helperFunctionTwo e φ₂

  return (φ₄ , TyTCatch tr₁ tr₂ e∈Ξ e∈φ₁ e∉φ₂ φ₃-proof φ₄-proof)

checkType Ξ Γ (TIfThenElse cond term₁ term₂) ty = do
  -- Check the type of the condition and infer the types of the then- and else-branches.
  (bool , (φ₁ , tr₁)) ← inferType Ξ Γ cond
    where _ → evalError "If-then-else condition should have a boolean type!"
  (φ₂ , tr₂) ← checkType Ξ Γ term₁ ty
  (φ₃ , tr₃) ← checkType Ξ Γ term₂ ty

  -- Sum the annotations of the condition and the then- and else-branches.
  let (φ₄ , φ₄-proof) = mergeAnn φ₁ φ₂
      (φ₅ , φ₅-proof) = mergeAnn φ₃ φ₄

  return (φ₅ , TyTIfThenElse tr₁ tr₂ tr₃ φ₄-proof φ₅-proof)

checkType Ξ Γ term ty = do
  (t , (φ , tr)) ← inferType Ξ Γ term
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return (φ , tr)
