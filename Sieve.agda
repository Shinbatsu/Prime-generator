module Sieve where

open import Algebra
open import Coinduction
open import Data.Empty
open import Data.Maybe
open import Data.Nat hiding (compare; _<_; _≟_)
open import Data.Nat.Coprimality
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤)

open import Relation.Binary.StrictTotalOrder Data.Nat.Properties.strictTotalOrder
open StrictTotalOrder Data.Nat.Properties.strictTotalOrder
open WithTotalOrder ℕ _<_ (StrictTotalOrder.isStrictTotalOrder Data.Nat.Properties.strictTotalOrder) NatBoundedGtWF.wf

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; _≢_)

private
  module ≤O = DecTotalOrder Data.Nat.Properties.≤-decTotalOrder
  module <O  = StrictTotalOrder Data.Nat.Properties.strictTotalOrder

abstract 
 z' : ∀ {a b} → a ≤ b → ¬ a ≡ b → a < b
 z' .{0} {zero} z≤n neqqq = ⊥-elim (neqqq PropEq.refl) 
 z' .{0} {suc n} z≤n neqqq = s≤s z≤n
 z' .{suc m} .{suc n} (s≤s {m} {n} m≤n) neqqq = s≤s (z' m≤n (λ x → neqqq (PropEq.cong suc x)))
