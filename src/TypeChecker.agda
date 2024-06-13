module TypeChecker {name : Set} where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import Data.String hiding (_++_)
open import Exceptions {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope
open import Util.Annotation
open import Relation.Nullary

open import Agda.Builtin.Equality
open import Data.Product
open import Data.List
open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name
  u : Term α

convert_ann : (a b : Ann) → Evaluator (a ≡ b)
convert_ann ∅ ∅ = return refl
convert_ann (φ₁ +++ s₁) (φ₂ +++ s₂) with s₁ ≟ s₂
... | yes refl = do
  refl <- convert_ann φ₁ φ₂
  return refl
... | no _ = evalError "unequal exceptions"
convert_ann _ _ = evalError "unequal exceptions"

-- convert_list : (a b : List String) → Evaluator (a ≡ b)
-- convert_list [] [] = return refl
-- convert_list (x ∷ xs) (y ∷ ys) with x ≟ y
-- ... | yes refl = do
--   refl <- convert_list xs ys
--   return refl
-- ... | no _ = evalError "unequal exceptions"
-- convert_list _ _ = evalError "unequal exceptions"

-- Type checking function application requires conversion checking,
-- i.e. checking whether two types are equal.
--
convert : (a b : Type) → Evaluator (a ≡ b)
convert nat nat = return refl
convert bool bool = return refl
-- convert (la [ lφ ]⇒ lb) (ra [ rφ ]⇒ rb) = do
--   refl ← convert la ra
--   refl ← convert lb rb
--   refl ← convert_list lφ rφ
--   return refl
convert _ _ = evalError "unequal types"

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Ξ : List String) (Γ : Context Type α) u             (ann : Ann) → Evaluator (Σ[ t ∈ Type ] Ξ ◂ Γ ⊢ u ∶ t ∣ ann)
checkType : ∀ (Ξ : List String) (Γ : Context Type α) u (ty : Type) (ann : Ann) → Evaluator (Ξ ◂ Γ ⊢ u ∶ ty ∣ ann)

-- checkAnn takes a term and basically just checks if there any exceptions, if there are then it just adds it to a list.
checkAnn  : Term α → Ann
checkAnn (TLam _ body) = checkAnn body
checkAnn (TVar _ _) = ∅
checkAnn (term ↓ _) = ∅
checkAnn (TIfThenElse cond u v) = ∅
checkAnn (TDecl _ _) = ∅

inferType Ξ ctx (TVar x index) exc = return (lookupVar ctx x index , TyTVar index)
inferType Ξ ctx (TLam x body) exc = evalError "cannot infer the type of a lambda"
inferType Ξ ctx (TRaise e) exc = evalError "cannot infer the type of a raising error"
-- inferType Ξ ctx (TCatch e teTerm faTerm) exc = evalError "cannot infer the type of catching block"
inferType Ξ ctx (TDecl e term) exc = evalError "cannot infer the type of an exception declaration"
inferType Ξ ctx (TIfThenElse e tTerm eTerm) exc = evalError "cannot infer the type of an if-statement declaration"

-- inferType Ξ ctx (TApp lam arg) exc = do
--   let φ₂ = checkAnn lam
--   let φ₃ = checkAnn arg

--   (a [ φ₁ ]⇒ b , gtu) ← inferType Ξ ctx lam φ₂
--     where _ → evalError "application head should have a function type"
  
--   gtv ← checkType Ξ ctx arg a φ₃
  
--   refl ← convert_list (φ₁ ++ φ₂ ++ φ₃) exc
  
--   return (b , TyTApp gtu gtv)

inferType Ξ ctx (term ↓ type) exc = do
  tr ← checkType Ξ ctx term type exc
  return (type , TyTAnn tr)
  
checkType Ξ ctx (TLam x body) (a [ φ ]⇒ b) exc = do
  let (φ₃ , φ₃-proof) = mergeAnn φ exc
  tr ← checkType Ξ (ctx , x ∶ a) body b φ₃ 
  return (TyTLam tr φ₃-proof)
checkType _ _ (TLam _ _) _ _ = evalError "lambda should have a function type"
checkType Ξ ctx (TDecl e term) ty exc = do
  tr ← checkType (e ∷ Ξ) ctx term ty exc
  return (TyTDecl tr)
checkType Ξ ctx (TRaise e) ty exc with e ∈? Ξ | e ∈ₐ? exc
...                             | yes (e∈Ξ)   | yes (e∈ₐexc) = return (TyTRaise e∈Ξ e∈ₐexc)
...                             | _           | _           = evalError "raising an exception that has not been declared"
-- checkType Ξ ctx (TCatch e teTerm faTerm) ty exc with e ∉? exc
-- ...                             | yes e∉exc                 = do
--                                     let φ₁ = checkAnn teTerm
--                                     let φ₂ = checkAnn faTerm

--                                     refl ← convert_list (φ₁ ∖ (set e) ++ φ₂) exc

--                                     tr₁ ← checkType Ξ ctx teTerm ty φ₁
--                                     tr₂ ← checkType Ξ ctx faTerm ty φ₂
--                                     return (TyTCatch tr₁ tr₂)
-- ...                             | no _                      = evalError "checking an exception that's already covered"
checkType Ξ ctx (TIfThenElse cond tTerm eTerm) ty exc = do
  let φ₁ = checkAnn cond
      φ₂ = checkAnn tTerm
      φ₃ = checkAnn eTerm
      (φ₄ , φ₄-proof) = mergeAnn φ₁ φ₂
      (φ₅ , φ₅-proof) = mergeAnn φ₃ φ₄

  (bool , tr₁) ← inferType Ξ ctx cond φ₁
    where _ → evalError "if-then condition should have a boolean type"
  tr₂ ← checkType Ξ ctx tTerm ty φ₂
  tr₃ ← checkType Ξ ctx eTerm ty φ₃

  refl ← convert_ann φ₅ exc
    
  return (TyTIfThenElse tr₁ tr₂ tr₃ φ₄-proof φ₅-proof)
checkType Ξ ctx term ty exc = do
  (t , tr) ← inferType Ξ ctx term exc
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr    