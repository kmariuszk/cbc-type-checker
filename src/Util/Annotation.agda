module Util.Annotation where

open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid
open import Data.List
open import Data.String
open import Relation.Nullary
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Function.Base using (case_of_; _$_)

data Ann : Set where
  ∅ : Ann
  _+++_ : Ann → String → Ann

infix 3  _∪_≡_

data _∪_≡_ : Ann → Ann → Ann → Set where
  empty : ∀ {φ} → φ ∪ ∅ ≡ φ
  append : ∀ {φ₁ φ₂ φ₃ v} → φ₁ ∪ φ₂ ≡ φ₃ → φ₁ ∪ (φ₂ +++ v) ≡ (φ₃ +++ v)

mergeAnn : (φ₁ φ₂ : Ann) → Σ[ φ₃ ∈ Ann ] φ₁ ∪ φ₂ ≡ φ₃
mergeAnn φ₁ ∅ = φ₁ , empty
mergeAnn φ₁ (φ₂ +++ x) with mergeAnn φ₁ φ₂
... | φ₃ , φ₃-proof = (φ₃ +++ x) , append φ₃-proof

-- Definition of a new datatype to prove membership of a string in Ann
data _∈ₐ_ : String → Ann → Set where
  hereₐ : ∀ {v φ} → v ∈ₐ (φ +++ v)
  thereₐ : ∀ {v w φ} → v ∈ₐ φ → v ∈ₐ (φ +++ w)

-- Proof generator of membership
_∈ₐ?_ : (x : String) (set : Ann) → Dec (x ∈ₐ set)
x ∈ₐ? ∅ = no (λ ())
x ∈ₐ? (φ +++ a) with x ≟ a
... | yes refl = yes hereₐ
... | no x≢a with x ∈ₐ? φ
...    | yes p = yes (thereₐ p)
...    | no n = no (λ { hereₐ → contradiction refl x≢a ; (thereₐ p') → n p' })