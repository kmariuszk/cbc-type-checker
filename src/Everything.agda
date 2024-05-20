module Everything where

open import Agda.Builtin.String

name = String

open import Exceptions {name}
open import TypeChecker {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  id-fun : Term sempty
  id-fun = TLam "x" (TVar "x" here)

  id-type : Type
  id-type = nat [ aempty ]⇒ nat

  id-tc : Evaluator (eempty ◂ cempty ⊢ id-fun ∶ id-type ∣ aempty)
  id-tc = checkType eempty cempty id-fun id-type aempty

  test-id : id-tc ≡ return (TyTLam (TyTVar here))
  test-id = refl
