module Util.Annotation where
  
open import Data.String.Properties
open import Data.List.Membership.DecSetoid ≡-decSetoid

open import Data.Product
open import Data.String
open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; _≢_)

data Ann : Set where
  ∅ : Ann
  _+++_ : String → Ann → Ann

infix 3  _∪_≡_

data _∪_≡_ : Ann → Ann → Ann → Set where
  empty : ∀ {φ} → φ ∪ ∅ ≡ φ
  append : ∀ {φ₁ φ₂ φ₃ v} → φ₁ ∪ φ₂ ≡ φ₃ → φ₁ ∪ (v +++ φ₂) ≡ (v +++ φ₃)

mergeAnn : (φ₁ φ₂ : Ann) → Σ[ φ₃ ∈ Ann ] φ₁ ∪ φ₂ ≡ φ₃
mergeAnn φ₁ ∅ = φ₁ , empty
mergeAnn φ₁ (x +++ φ₂) with mergeAnn φ₁ φ₂
... | φ₃ , φ₃-proof = (x +++ φ₃) , append φ₃-proof

-- `_∈ₐ_` datatype to prove membership of a String in Ann
data _∈ₐ_ : String → Ann → Set where
  hereₐ : ∀ {v φ} → v ∈ₐ (v +++ φ)
  thereₐ : ∀ {v w φ} → v ∈ₐ φ → v ∈ₐ (w +++ φ)

-- Membership proof generator
_∈ₐ?_ : (x : String) (set : Ann) → Dec (x ∈ₐ set)
x ∈ₐ? ∅ = no (λ ())
x ∈ₐ? (a +++ φ) with x ≟ a
... | yes refl = yes hereₐ
... | no x≢a with x ∈ₐ? φ
...    | yes p = yes (thereₐ p)
...    | no n = no (λ { hereₐ → contradiction refl x≢a ; (thereₐ p') → n p' })

-- Subtraction of a single element
infix 4 _-_≡_

data _-_≡_ : Ann → String → Ann → Set where
  remove-here : ∀ {v φ} → (v +++ φ) - v ≡ φ
  remove-there : ∀ {v w φ φ₃} → φ - v ≡ φ₃ → (w +++ φ) - v ≡ (w +++ φ₃)
  remove-not-present : ∀ {φ x} → ¬ (x ∈ₐ φ) → φ - x ≡ φ

-- Subtraction proof generator
removeAnn : (φ : Ann) (x : String) → Σ[ φ₃ ∈ Ann ] φ - x ≡ φ₃
removeAnn ∅ x = ∅ , remove-not-present (λ ()) -- If the annotation list is empty, nothing to remove
removeAnn (a +++ φ) x with x ≟ a
... | yes refl = φ , remove-here -- If the element matches the head, remove it
... | no x≢a with removeAnn φ x
...    | φ₃ , p = (a +++ φ₃) , remove-there p -- Recur on the tail
