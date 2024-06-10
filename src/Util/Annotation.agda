module Util.Annotation where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid
open import Data.List
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open import Data.Bool hiding (_≟_)

Ann = List String

∅ : Ann
∅ = []

infixr 5 _∪_

-- Set union of two lists of annotations
_∪_ : Ann → Ann → Ann
[] ∪ ys = ys
(x ∷ xs) ∪ ys with x ∈? ys
... | yes _ = xs ∪ ys
... | no _ = x ∷ (xs ∪ ys)

-- Helper function to remove a specific element from a list
remove : String → Ann → Ann
remove y [] = []
remove y (x ∷ xs) with x ≟ y
... | yes _ = xs
... | no _ = x ∷ remove y xs

-- Set difference between two lists of annotations
_∖_ : Ann → Ann → Ann
xs ∖ [] = xs
xs ∖ (y ∷ ys) with y ∈? xs
... | yes _ = (remove y xs) ∖ ys
... | no _ = xs ∖ ys

set : String → Ann
set e = e ∷ []

-- -- Helper to check if two lists are equal when treated as sets
-- equalSets : Ann → Ann → Bool
-- equalSets xs ys = all (∈ ys) xs && all (∈ xs) ys

-- -- Prove union is associative, which is helpful for proving more complex properties
-- assocUnion : ∀ (φ₁ φ₂ φ₃ : Ann) → (φ₁ ∪ (φ₂ ∪ φ₃)) ≡ ((φ₁ ∪ φ₂) ∪ φ₃)
-- assocUnion [] φ₂ φ₃ = refl
-- assocUnion (x ∷ φ₁) φ₂ φ₃ with x ∈? (φ₁ ∪ (φ₂ ∪ φ₃))
-- ... | no _ = cong (x ∷_) (assocUnion φ₁ φ₂ φ₃)
-- ... | yes _ = assocUnion φ₁ φ₂ φ₃  -- assuming duplicates do not affect equality

-- -- Function to check if union of two lists equals another list
-- checkUnionEqual : Ann → Ann → Ann → Bool
-- checkUnionEqual φ₁ φ₂ φ₃ = equalSets (φ₁ ∪ φ₂) φ₃