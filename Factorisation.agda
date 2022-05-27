module Factorisation where

open import Data.Nat
open import Data.Nat.Properties hiding (+-comm; *-assoc)
open import Data.Nat.Divisibility
open import Algebra
open CommutativeSemiring Data.Nat.Properties.commutativeSemiring using (+-comm; *-assoc)
open import Data.List hiding (any)
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.Sum
open import Function
open import Data.Product
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; _≢_; setoid; refl; trans; sym; subst)
open import Relation.Nullary
open import Data.Empty

IsPrime1 : ℕ → Set
IsPrime1 n = ∀ m → m ∣ n → m ≡ n ⊎ m ≡ 1
 
IsPrime : ℕ → Set
IsPrime n = n ≢ 1 × IsPrime1 n

IsPrime' : ℕ → Set
IsPrime' n = n > 1 × (∀ m → (m<n : m < n) → IsPrime m → ¬ m ∣ n)

open import Induction.WellFounded
open import Induction.Nat

Prime : Set
Prime = Σ ℕ IsPrime
