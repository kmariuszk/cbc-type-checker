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

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  {- This code tests λ x → x -} 

  id-fun : Term sempty
  id-fun = TLam "x" (TVar "x" hereₛ)

  id-type : Type
  id-type = nat [ aempty ]⇒ nat

  id-tc : Evaluator (eempty ◂ cempty ⊢ id-fun ∶ id-type ∣ aempty)
  id-tc = checkType eempty cempty id-fun id-type aempty

  test-id : id-tc ≡ return (TyTLam (TyTVar hereₛ))
  test-id = refl

  {- This code tests the most basic TRaise case with pre-declared exception "ex" -} 

  simple-raise-fun : Term sempty
  simple-raise-fun = TRaise "ex"
  
  simple-raise-type : Type
  simple-raise-type = nat

  exceptions-raise : List String
  exceptions-raise = "ex" ∷ []

  annotations-raise : List String
  annotations-raise = "ex" ∷ []

  simple-raise-tc : Evaluator (exceptions-raise ◂ cempty ⊢ simple-raise-fun ∶ simple-raise-type ∣ annotations-raise)
  simple-raise-tc = checkType exceptions-raise cempty simple-raise-fun simple-raise-type annotations-raise

  test-simple-raise : simple-raise-tc ≡ return (TyTRaise (here refl) (here refl))
  test-simple-raise = refl

  {- This code tests a simple catch block -}

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

  annotations : List String
  annotations = "ex" ∷ []

  simple-catch-tc : Evaluator (exceptions ◂ context ⊢ simple-catch-fun ∶ simple-catch-type ∣ aempty)
  simple-catch-tc = checkType exceptions context simple-catch-fun simple-catch-type aempty

  test-simple-catch : simple-catch-tc ≡ return (TyTCatch (λ ()) (TyTRaise (here refl) (here refl)) (TyTVar hereₛ))
  test-simple-catch = refl

  {- This code tests a lambda which doesn't throw any errors but has a catch block in its body -} 

  simple-exception-fun : Term sempty
  simple-exception-fun = TDecl "ex" (TLam "x" (TCatch "ex"
                                     (TRaise "ex")
                                     (TVar "x" hereₛ)))

  simple-exception-type : Type
  simple-exception-type = nat [ aempty ]⇒ nat

  simple-exception-tc : Evaluator (eempty ◂ cempty ⊢ simple-exception-fun ∶ simple-exception-type ∣ aempty)
  simple-exception-tc = checkType eempty cempty simple-exception-fun simple-exception-type aempty

  test-simple-exception : simple-exception-tc ≡ return (TyTDecl (TyTLam (TyTCatch (λ ()) (TyTRaise (here refl) (here refl)) (TyTVar hereₛ))))
  test-simple-exception = refl
  