module Everything where

open import Agda.Builtin.String

name = String

open import Exceptions {name}
open import TypeChecker {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope
open import Data.List
open import Data.Empty
open import Data.List.Relation.Unary.Any
open import Util.Annotation

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  {- This code tests λ x → x -} 

  id-fun : Term sempty
  id-fun = TLam "x" (TVar "x" hereₛ)

  id-type : Type
  id-type = nat [ ∅ ]⇒ nat

  id-tc : Evaluator ([] ◂ cempty ⊢ id-fun ∶ id-type ∣ ∅)
  id-tc = checkType [] cempty id-fun id-type ∅

  test-id : id-tc ≡ return (TyTLam (TyTVar hereₛ) _∪_≡_.empty)
  test-id = refl

  -- {- This code tests the most basic TRaise case with pre-declared exception "ex" -} 

  simple-raise-fun : Term sempty
  simple-raise-fun = TRaise "ex"
  
  simple-raise-type : Type
  simple-raise-type = unit

  exceptions-raise : List String
  exceptions-raise = "ex" ∷ []

  annotations-raise : Ann
  annotations-raise = ∅ +++ "ex"

  simple-raise-tc : Evaluator (exceptions-raise ◂ cempty ⊢ simple-raise-fun ∶ simple-raise-type ∣ annotations-raise)
  simple-raise-tc = checkType exceptions-raise cempty simple-raise-fun simple-raise-type annotations-raise

  test-simple-raise : simple-raise-tc ≡ return (TyTRaise (here refl) (hereₐ))
  test-simple-raise = refl

  -- {- This code tests a simple catch block -}

  scope : Scope name
  scope = "x" ∷ sempty

  simple-catch-fun : Term scope
  simple-catch-fun = (TCatch "ex"
                                     (TRaise "ex")
                                     (TVar "x" hereₛ))
  
  simple-catch-type : Type
  simple-catch-type = nat

  context : Context Type scope
  context = cempty , "x" ∶ nat

  exceptions : List String
  exceptions = "ex" ∷ []

  simple-catch-tc : Evaluator (exceptions ◂ context ⊢ simple-catch-fun ∶ simple-catch-type ∣ ∅)
  simple-catch-tc = checkType exceptions context simple-catch-fun simple-catch-type ∅

  test-simple-catch : simple-catch-tc ≡ return (TyTCatch (TyTRaise (here refl) (here refl)) (TyTVar hereₛ))
  test-simple-catch = refl

  -- {- This code tests a lambda which doesn't throw any errors but has a catch block in its body -} 

  -- simple-exception-fun : Term sempty
  -- simple-exception-fun = TDecl "ex" (TLam "x" (TCatch "ex"
  --                                    (TRaise "ex")
  --                                    (TVar "x" hereₛ)))

  -- simple-exception-type : Type
  -- simple-exception-type = nat [ aempty ]⇒ nat

  -- simple-exception-tc : Evaluator (eempty ◂ cempty ⊢ simple-exception-fun ∶ simple-exception-type ∣ aempty)
  -- simple-exception-tc = checkType eempty cempty simple-exception-fun simple-exception-type aempty

  -- test-simple-exception : simple-exception-tc ≡ return (TyTDecl (TyTLam (TyTCatch (λ ()) (TyTRaise (here refl) (here refl)) (TyTVar hereₛ))))
  -- test-simple-exception = refl

  {- This code tests a simple if-then term -}

  scope₂ : Scope name
  scope₂ = "x" ∷ "y" ∷ sempty

  simple-if-fun : Term scope₂
  simple-if-fun = TIfThenElse (TVar "x" hereₛ) (TVar "y" (thereₛ hereₛ)) (TVar "y" (thereₛ hereₛ))

  simple-if-type : Type
  simple-if-type = nat

  context₂ : Context Type scope₂
  context₂ = (cempty , "y" ∶ nat) , "x" ∶ bool

  simple-if-tc : Evaluator ([] ◂ context₂ ⊢ simple-if-fun ∶ simple-if-type ∣ ∅)
  simple-if-tc = checkType [] context₂ simple-if-fun simple-if-type ∅

  test-simple-if : simple-if-tc ≡ return (TyTIfThenElse (TyTVar hereₛ) (TyTVar (thereₛ hereₛ)) (TyTVar (thereₛ hereₛ)) _∪_≡_.empty _∪_≡_.empty)
  test-simple-if = refl 
  
  {- This code tests an if-then which can throw an exception within a lambda -} 
  
  -- scope₂ : Scope name
  -- scope₂ = "x" ∷ "y" ∷ sempty

  -- simple-if-fun : Term scope₂
  -- simple-if-fun = TIfThen (TVar "x" hereₛ) (TVar "y" (thereₛ hereₛ))

  -- simple-if-type : Type
  -- simple-if-type = nat

  -- context₂ : Context Type scope₂
  -- context₂ = (cempty , "y" ∶ nat) , "x" ∶ bool

  -- simple-if-tc : Evaluator (eempty ◂ context₂ ⊢ simple-if-fun ∶ simple-if-type ∣ aempty)
  -- simple-if-tc = checkType eempty context₂ simple-if-fun simple-if-type aempty

  -- test-simple-if : simple-if-tc ≡ return (TyTIfThen (TyTVar hereₛ) (TyTVar (thereₛ hereₛ)))
  -- test-simple-if = refl 