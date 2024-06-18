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

open import Agda.Builtin.Equality
open import Data.Product
open import Data.List
open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name
  u : Term α

-- Checking whether two annotations are equal.
convertAnn : (a b : Ann) → Evaluator (a ≡ b)
convertAnn ∅ ∅ = return refl
convertAnn (s₁ +++ φ₁) (s₂ +++ φ₂) with s₁ ≟ s₂
... | yes refl = do
  refl <- convertAnn φ₁ φ₂
  return refl
... | no _ = evalError "unequal exceptions 2"
convertAnn ∅ _ = evalError "unequal exceptions 3"
convertAnn _ ∅ = evalError "unequal exceptions 4"

-- Checking whether two types are equal.
convert : (a b : Type) → Evaluator (a ≡ b)
convert nat nat = return refl
convert bool bool = return refl
convert (la [ lφ ]⇒ lb) (ra [ rφ ]⇒ rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  refl ← convertAnn lφ rφ
  return refl
convert _ _ = evalError "unequal types"

-- Given specific input term, `checkAnn` inspects what exceptions it can throw
-- (it traverses until it reaches TCatch or any other term without subterms)
checkAnn  : Term α → Ann
checkAnn (TVar _ _) = ∅
checkAnn (TLam _ body) = checkAnn body
checkAnn (TApp lam arg) = let φ₁ = checkAnn lam
                              φ₂ = checkAnn arg
                              (φ₃ , _) = mergeAnn φ₁ φ₂                             
                          in  φ₃
checkAnn (TRaise e) = e +++ ∅
checkAnn (TDecl _ body) = checkAnn body
-- Once we reach TCatch term, we stop traversing and return the exceptions that can be thrown (since all other exceptions are covered by the catch block)
checkAnn (TCatch e teTerm faTerm) = ∅
checkAnn (TIfThenElse cond u v) = let φ₁ = checkAnn cond
                                      φ₂ = checkAnn u
                                      φ₃ = checkAnn v
                                      (φ₄ , _) = mergeAnn φ₁ φ₂
                                      (φ₅ , _) = mergeAnn φ₃ φ₄                                
                                  in  φ₅
-- We skip the declaration, we only look for TRaise terms (problem: TCatch within a TCatch)
checkAnn (term ↓ (a [ φ₁ ]⇒ b)) = checkAnn term 
-- In the language we are considering, we do not have any other terms that can throw exceptions
checkAnn (_ ↓ _) = ∅

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Ξ : List String) (Γ : Context Type α) u             (ann : Ann) → Evaluator (Σ[ t ∈ Type ] Ξ ◂ Γ ⊢ u ∶ t ∣ ann)
checkType : ∀ (Ξ : List String) (Γ : Context Type α) u (ty : Type) (ann : Ann) → Evaluator (Ξ ◂ Γ ⊢ u ∶ ty ∣ ann)

inferType Ξ Γ (TVar x index) φ = return (lookupVar Γ x index , TyTVar index)
inferType Ξ Γ (TLam x body) φ = evalError "cannot infer the type of a lambda"
inferType Ξ Γ (TRaise e) φ = evalError "cannot infer the type of a raising error"
inferType Ξ Γ (TCatch e teTerm faTerm) φ = evalError "cannot infer the type of catching block"
inferType Ξ Γ (TDecl e term) φ = evalError "cannot infer the type of an exception declaration"
inferType Ξ Γ (TIfThenElse e tTerm eTerm) φ = evalError "cannot infer the type of an if-statement declaration"
inferType Ξ Γ (TApp lam arg) φ₀ = do
  let φ₂ = checkAnn lam

  (a [ φ₁ ]⇒ b , gtu) ← inferType Ξ Γ lam φ₂
    where _ → evalError "application head should have a function type"
  
  let φ₃ = checkAnn arg
      (φ₄ , φ₄-proof) = mergeAnn φ₁ φ₂
      (φ₅ , φ₅-proof) = mergeAnn φ₃ φ₄

  gtv ← checkType Ξ Γ arg a φ₃
  
  refl ← convertAnn φ₅ φ₀
  
  return (b , TyTApp gtu gtv φ₄-proof φ₅-proof)
inferType Ξ Γ (term ↓ type) φ₀ = do
  tr ← checkType Ξ Γ term type φ₀
  return (type , TyTAnn tr)
  
checkType Ξ Γ (TLam x body) (a [ φ₁ ]⇒ b) φ₀ = do
  -- Note: φ₂ may contain duplicates!
  let (φ₂ , φ₂-proof) = mergeAnn φ₁ φ₀
  tr ← checkType Ξ (Γ , x ∶ a) body b φ₂
  return (TyTLam tr φ₂-proof)
checkType _ _ (TLam _ _) _ _ = evalError "lambda should have a function type"
checkType Ξ Γ (TDecl e term) ty φ₀ = do
  tr ← checkType (e ∷ Ξ) Γ term ty φ₀
  return (TyTDecl tr)
checkType Ξ Γ (TRaise e) ty φ₀ with e ∈? Ξ | e ∈ₐ? φ₀
...                             | yes (e∈Ξ)   | yes (e∈ₐφ₀) = return (TyTRaise e∈Ξ e∈ₐφ₀)
...                             | yes _       | _           = evalError "raising an exception that has not been annotated"
...                             | _           | yes _       = evalError "raising an exception that has not been declared"
...                             | _           | _           = evalError "raising an exception that has neither been declared or annotated"
checkType Ξ Γ (TCatch e teTerm faTerm) ty φ₀ with e ∈ₐ? φ₀
...                             | no e∉φ₀                 = do
                                    let φ₁ = checkAnn teTerm
                                        φ₂ = checkAnn faTerm
                                        (φ₃ , φ₃-proof) = mergeAnn φ₁ φ₂

                                    refl ← convertAnn φ₃ φ₀

                                    tr₁ ← checkType Ξ Γ teTerm ty (e +++ φ₁)
                                    tr₂ ← checkType Ξ Γ faTerm ty φ₂
                                    
                                    return (TyTCatch tr₁ tr₂ φ₃-proof)
...                             | yes _                      = evalError "checking an exception that's already covered"
checkType Ξ Γ (TIfThenElse cond tTerm eTerm) ty φ₀ = do
  let φ₁ = checkAnn cond
      φ₂ = checkAnn tTerm
      φ₃ = checkAnn eTerm
      (φ₄ , φ₄-proof) = mergeAnn φ₁ φ₂
      (φ₅ , φ₅-proof) = mergeAnn φ₃ φ₄

  refl ← convertAnn φ₅ φ₀
  
  (bool , tr₁) ← inferType Ξ Γ cond φ₁
    where _ → evalError "if-then condition should have a boolean type"
  tr₂ ← checkType Ξ Γ tTerm ty φ₂
  tr₃ ← checkType Ξ Γ eTerm ty φ₃
    
  return (TyTIfThenElse tr₁ tr₂ tr₃ φ₄-proof φ₅-proof)
checkType Ξ Γ term ty φ₀ = do
  (t , tr) ← inferType Ξ Γ term φ₀
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr     