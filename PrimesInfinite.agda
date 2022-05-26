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


∈Map : ∀ {A B : Set} →  (f : A → B) → ∀ {l} →
  let 
    module M₁ = Membership (PropEq.setoid A)
    module M₂ = Membership (PropEq.setoid B) in
  ∀ {x} →
  M₁._∈_ x l
  → M₂._∈_ (f x) (Data.List.map f l)
∈Map f {l} {x} inn = anyMap f (PropEq.cong f) inn

procuct-preserves-≥1 : ∀ {l} → All (λ q → q ≥ 1) l → (λ q → q ≥ 1) (product l)
procuct-preserves-≥1 [] = s≤s z≤n
procuct-preserves-≥1 (px ∷ pxs) = px *-mono procuct-preserves-≥1 pxs

infinite : ∀ n → ∃ (λ m → n < m × (∀ x → x ≤ n → IsPrime x → ¬ x ∣ m))
infinite n = m , m>n , correct where
  open import Data.List
  prms = primesTo (suc n)

  rawPrimes = Data.List.map proj₁ (proj₁ prms)
  pprod = product rawPrimes
