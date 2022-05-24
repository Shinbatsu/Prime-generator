module PrimesInfinite where

open import Algebra
open import CommutativeSemiring commutativeSemiring
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.List.Membership.Setoid (setoid ℕ)
open import Data.Maybe hiding (Any; All)
open import Data.Nat hiding (_*_; _+_)
open import Data.Nat.Divisibility
open import Data.Nat.Properties hiding (+-comm; *-comm)
open import Data.Product
open import Factorisation
open import Relation.Binary
open import Relation.Nullary

import Data.List.Membership.Setoid
import MRel
import Relation.Binary.PropositionalEquality as PropEq
import Data.Nat.Divisibility as Div

open Div
open MRel _<_
open PropEq using (_≡_)
open SemiringSolver

theorem : ∀ {x l} → x ∈ l → x ∣ product l
theorem {l = x ∷ t} (here refl) = divides (product t) (solve 2 (λ a b → a :* b := b :* a) refl x (product t))
theorem {l = x ∷ t} (there pxs) with theorem pxs
theorem {l = x ∷ t} (there pxs) | th = Poset.trans Div.poset th (divides x refl)
theorem {l = []} ()

module Membership = Data.List.Membership.Setoid

anyMap : ∀ {A B : Set} → (f : A → B) → {P₁ : A → Set} → {P₂ : B → Set} → (f-preserves : ∀ {x} → P₁ x → P₂ (f x))
  → ∀ {l} → Any P₁ l → Any P₂ (Data.List.map f  l)
anyMap f pres (here px) = here (pres px)
anyMap f pres (there pxs) = there (anyMap f pres pxs)

allMap : ∀ {A B : Set} → (f : A → B) → {P₁ : A → Set} → {P₂ : B → Set} → (f-preserves : ∀ {x} → P₁ x → P₂ (f x))
  → ∀ {l} → All P₁ l → All P₂ (Data.List.map f  l)
allMap f pres [] = []
allMap f pres (px ∷ pxs) = pres px ∷ allMap f pres pxs
