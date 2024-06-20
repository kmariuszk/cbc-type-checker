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
open import Data.Product

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  {- This code tests λ x → x -} 

  id-fun : Term sempty
  id-fun = TLam "x" (TVar "x" hereₛ)

  id-type : Type
  id-type = nat [ ∅ ]⇒ nat

  id-tc : Evaluator (Σ[ φ ∈ Ann ] [] ◂ cempty ⊢ id-fun ∶ id-type ∣ φ)
  id-tc = checkType [] cempty id-fun id-type

  test-id : id-tc ≡ return (∅ , (TyTLam (TyTVar hereₛ)))
  test-id = refl

  -- {- This code tests the most basic TRaise case with pre-declared exception "ex" -} 

  simple-raise-fun : Term sempty
  simple-raise-fun = TRaise "ex"
  
  simple-raise-type : Type
  simple-raise-type = nat

  exceptions-raise : List String
  exceptions-raise = "ex" ∷ []

  simple-raise-tc : Evaluator (Σ[ φ ∈ Ann ] exceptions-raise ◂ cempty ⊢ simple-raise-fun ∶ simple-raise-type ∣ φ)
  simple-raise-tc = checkType exceptions-raise cempty simple-raise-fun simple-raise-type

  test-simple-raise : simple-raise-tc ≡ return (("ex" +++ ∅) , (TyTRaise ((here refl))))
  test-simple-raise = refl

  -- {- This code tests a simple if-then term -}

  scope₂ : Scope name
  scope₂ = "x" ∷ "y" ∷ sempty

  simple-if-fun : Term scope₂
  simple-if-fun = TIfThenElse (TVar "x" hereₛ) (TVar "y" (thereₛ hereₛ)) (TVar "y" (thereₛ hereₛ))

  simple-if-type : Type
  simple-if-type = nat

  context₂ : Context Type scope₂
  context₂ = (cempty , "y" ∶ nat) , "x" ∶ bool

  simple-if-tc : Evaluator (Σ[ φ ∈ Ann ] [] ◂ context₂ ⊢ simple-if-fun ∶ simple-if-type ∣ φ)
  simple-if-tc = checkType [] context₂ simple-if-fun simple-if-type

  test-simple-if : simple-if-tc ≡ return (∅ , (TyTIfThenElse (TyTVar hereₛ) (TyTVar (thereₛ hereₛ)) (TyTVar (thereₛ hereₛ)) _∪_≡_.empty _∪_≡_.empty))
  test-simple-if = refl 
  
  -- {- This code tests an if-then-else which can throw an exception within a lambda -} 
  
  scope₃ : Scope name
  scope₃ = "output" ∷ sempty

  if-with-exception-fun : Term scope₃
  if-with-exception-fun = 
    TDecl ("main-error") 
    (TDecl ("inner-error") 
      (TLam "cond1" 
        (TIfThenElse 
          (TVar "cond1" hereₛ) 
          (TLam "cond2" 
            (TIfThenElse 
              (TVar "cond2" hereₛ) 
              (TVar "output" (thereₛ (thereₛ hereₛ))) 
              (TRaise "inner-error"))) 
          (TRaise "main-error"))))


  if-with-exception-type : Type
  if-with-exception-type = bool [ "main-error" +++ ∅ ]⇒ (bool [ "inner-error" +++ ∅ ]⇒ nat)

  context₃ : Context Type scope₃
  context₃ = cempty , "output" ∶ nat

  if-with-exception-tc : Evaluator (Σ[ φ ∈ Ann ] [] ◂ context₃ ⊢ if-with-exception-fun ∶ if-with-exception-type ∣ φ)
  if-with-exception-tc = checkType [] context₃ if-with-exception-fun if-with-exception-type

  test-if-with-exception : if-with-exception-tc ≡ return (∅ , (TyTDecl (TyTDecl (TyTLam (TyTIfThenElse (TyTVar hereₛ) (TyTLam (TyTIfThenElse (TyTVar hereₛ) (TyTVar (thereₛ (thereₛ hereₛ))) (TyTRaise (here refl)) _∪_≡_.empty _∪_≡_.empty)) (TyTRaise (there (here refl))) _∪_≡_.empty _∪_≡_.empty)))))
  test-if-with-exception = refl 

  -- {- This code tests an application with catch and lambda terms -}

  scope₄ : Scope name
  scope₄ = "globalCondition" ∷ "output" ∷ "localCondition" ∷ "handleInner" ∷ "handleOuter" ∷ sempty

  app-with-catch-fun : Term scope₄
  app-with-catch-fun = 
    TDecl "Outer exception" 
      (TDecl "Inner exception" 
        (TCatch "Outer exception"
          -- Catch branch 
          (TCatch "Inner exception" 
            -- Catch branch
            (TApp 
              -- Annotated function
              (TLam "condition" 
                (TIfThenElse 
                  (TVar "condition" hereₛ) 
                  -- If condition holds...
                  (TIfThenElse 
                    (TVar "globalCondition" (thereₛ hereₛ)) 
                    -- If condition holds...
                    (TVar "output" (thereₛ (thereₛ hereₛ))) 
                    -- If condition does not hold...
                    (TRaise "Inner exception")) 
                  -- If condition does not hold...
                  (TRaise "Outer exception")) ↓ 
                (bool [ "Inner exception" +++ ("Outer exception" +++ ∅)]⇒ nat)) 
              -- Arguments
              (TVar "localCondition" (thereₛ (thereₛ hereₛ)))) 
            -- Handle branch
            (TVar "handleInner" (thereₛ (thereₛ (thereₛ (hereₛ)))))) 
          -- Handle branch
          (TVar "handleOuter" (thereₛ (thereₛ (thereₛ (thereₛ (hereₛ))))))))

  app-with-catch-type : Type
  app-with-catch-type = nat

  context₄ : Context Type scope₄
  context₄ = (((((cempty , "handleOuter" ∶ nat) , "handleInner" ∶ nat) , "localCondition" ∶ bool) , "output" ∶ nat) , "globalCondition" ∶ bool)

  app-with-catch-tc : Evaluator (Σ[ φ ∈ Ann ] [] ◂ context₄ ⊢ app-with-catch-fun ∶ app-with-catch-type ∣ φ)
  app-with-catch-tc = checkType [] context₄ app-with-catch-fun app-with-catch-type

  test-app-with-catch : app-with-catch-tc ≡ return (
    ∅ , 
    TyTDecl 
      (TyTDecl 
        (TyTCatch 
          (TyTCatch 
            (TyTApp 
              (TyTAnn 
                (TyTLam 
                  (TyTIfThenElse 
                    (TyTVar hereₛ) 
                    (TyTIfThenElse 
                      (TyTVar (thereₛ hereₛ)) 
                      (TyTVar (thereₛ (thereₛ hereₛ))) 
                      (TyTRaise (here refl)) 
                      _∪_≡_.empty 
                      _∪_≡_.empty
                    ) 
                    (TyTRaise (there (here refl))) 
                    (append _∪_≡_.empty) 
                    (append _∪_≡_.empty)
                  )
                )
              ) 
              (TyTVar (thereₛ (thereₛ hereₛ))) 
              (_∪_≡_.empty) 
              (append (append _∪_≡_.empty))
            ) 
            (TyTVar (thereₛ (thereₛ (thereₛ hereₛ))))
            (here refl)
            (hereₐ) 
            ((λ ())) 
            remove-here _∪_≡_.empty
        ) 
        (TyTVar (thereₛ (thereₛ (thereₛ (thereₛ hereₛ)))))
        (there (here refl)) 
        (hereₐ) 
        ((λ ())) 
        remove-here _∪_≡_.empty)))
  test-app-with-catch = refl  