module Util.Annotation where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid
open import Data.List
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Bool

Ann = List String

∅ : Ann
∅ = []

addUnique : String → Ann → Ann
addUnique str lst with str ∈? lst
... | yes _ = lst        -- If the string is already in the list, return the list unchanged
... | no  _ = str ∷ lst  -- If the string is not in the list, prepend it

infixr 5 _U_

_U_ : Ann → Ann → Ann
xs U [] = xs
xs U (y ∷ ys) = (addUnique y xs) U ys

removeUnique : String → Ann → Ann
removeUnique str lst = filterᵇ (λ x → (not (x != str))) lst

_∖_ : Ann → Ann → Ann
xs ∖ [] = xs
xs ∖ (y ∷ ys) = (removeUnique y xs) ∖ ys

set : String → Ann
set str = str ∷ []
