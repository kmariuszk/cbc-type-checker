module Everything where

open import Agda.Builtin.String

name = String

open import TypeChecker.Terms {name}
open import TypeChecker.Types
open import TypeChecker.TypingRules
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
  simple-raise-type = nat

  exceptions-raise : List String
  exceptions-raise = "ex" ∷ []

  annotations-raise : Ann
  annotations-raise = "ex" +++ ∅

  simple-raise-tc : Evaluator (exceptions-raise ◂ cempty ⊢ simple-raise-fun ∶ simple-raise-type ∣ annotations-raise)
  simple-raise-tc = checkType exceptions-raise cempty simple-raise-fun simple-raise-type annotations-raise

  test-simple-raise : simple-raise-tc ≡ return (TyTRaise (here refl) (hereₐ))
  test-simple-raise = refl

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
  
  {- This code tests an if-then-else which can throw an exception within a lambda -} 
  
  scope₃ : Scope name
  scope₃ = "x" ∷ "y" ∷ sempty

  if-with-exception-fun : Term scope₃
  if-with-exception-fun = TDecl 
    ("ex") 
    (
      (TLam 
        "z" 
        (TIfThenElse 
          ((TVar "z" ((hereₛ)))) 
          (TRaise "ex") 
          ((TVar "y" (thereₛ (thereₛ hereₛ)))))) 
    ↓ 
    ((bool [ "ex" +++ ∅ ]⇒ nat)))

  if-with-exception-type : Type
  if-with-exception-type = bool [ "ex" +++ ∅ ]⇒ nat

  context₃ : Context Type scope₃
  context₃ = (cempty , "y" ∶ nat) , "x" ∶ bool

  if-with-exception-tc : Evaluator ([] ◂ context₃ ⊢ if-with-exception-fun ∶ if-with-exception-type ∣ ∅)
  if-with-exception-tc = checkType [] context₃ if-with-exception-fun if-with-exception-type ∅

  test-if-with-exception : if-with-exception-tc ≡ return (
    TyTDecl (
      TyTAnn (
        TyTLam (
          TyTIfThenElse 
          (TyTVar hereₛ) 
          (TyTRaise (here refl) hereₐ) 
          (TyTVar (thereₛ (thereₛ hereₛ))) 
          (append _∪_≡_.empty) 
          (append _∪_≡_.empty)
        ) _∪_≡_.empty
    )))
  test-if-with-exception = refl 

  {- This code tests an application with multiple catch and lambda terms -}

  scope₄ : Scope name
  scope₄ = "inputOne" ∷ "inputTwo" ∷ "output" ∷ "defaultError" ∷ sempty

  app-with-catch-fun : Term scope₄
  app-with-catch-fun = TDecl 
    ("mainError")
    (TCatch 
      "mainError" 
      (TApp
        -- Lambda function 
        (TLam "conditionOne" 
          (TDecl "innerError" 
          (TCatch "innerError" 
            (TApp 
              (TLam "conditionTwo" 
                (TIfThenElse 
                  (TVar "conditionTwo" hereₛ) 
                  (TVar "output" (thereₛ (thereₛ (thereₛ (thereₛ hereₛ))))) 
                  (TRaise "innerError")) 
              ↓
              -- Function type 
              (nat [ "innerError" +++ ∅ ]⇒ nat)) 
            -- Argument for the function
            (TVar "inputTwo" (thereₛ (thereₛ hereₛ)))) 
          -- Handle annotation
          (TVar "defaultError" (thereₛ (thereₛ (thereₛ (thereₛ hereₛ))))))) 
          ↓ (bool [ "mainError" +++ ∅ ]⇒ nat)
      )
        -- Argument for the function 
      (TVar "inputOne" hereₛ)
    ) 
    -- Handle annotation
    (TVar "defaultError" (thereₛ (thereₛ (thereₛ hereₛ)))))

  -- app-with-catch-type : Type
  -- app-with-catch-type = nat

  -- context₄ : Context Type scope₄
  -- context₄ = (((cempty , "defaultError" ∶ nat) , "output" ∶ nat) , "inputTwo" ∶ nat) , "inputOne" ∶ bool

  -- app-with-catch-tc : Evaluator ([] ◂ context₄ ⊢ app-with-catch-fun ∶ app-with-catch-type ∣ ∅)
  -- app-with-catch-tc = checkType [] context₄ app-with-catch-fun app-with-catch-type ∅

  -- test-app-with-catch : app-with-catch-tc ≡ return ({!   !})
  -- test-app-with-catch = refl
