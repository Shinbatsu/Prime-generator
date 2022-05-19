module Multiples where

open import Data.Nat.Properties  
open import Data.Nat.Divisibility  

open import Algebra  
open CommutativeSemiring Data.Nat.Properties.commutativeSemiring using (+-comm; *-comm; *-identity)  

open import SortedStream  
open import Relation.Nullary  
import Relation.Binary.PropositionalEquality as PropEq  
open import Relation.Binary  
open import Coinduction  

open import Data.Nat
open import Data.Product
open import Data.Maybe

getBound : ℕ → ℕ → Maybe ℕ  
getBound _ zero = nothing  
getBound n (suc k) = just (k * n)  

private  
 module ≤O = DecTotalOrder Data.Nat.Properties.≤-decTotalOrder  
 module <O = StrictTotalOrder Data.Nat.Properties.strictTotalOrder

abstract  
 multiples' : ∀ n (k : ℕ) → n > 0 → SortedStream _<_ (λ x → n ∣ x) (getBound n k)  
 multiples' n k n>0 = (minimum (k * n) (divides k PropEq.refl , good) (minimal k)) ∷ ♯ multiples' n (suc k) n>0 where  

  +-lem-inv : ∀ {n a b} → a ≤ b → n + a ≤ n + b  
  +-lem-inv {zero} le = le  
  +-lem-inv {suc n} le = s≤s (+-lem-inv {n} le)  

  +-lem : ∀ {n a b} → n + a ≤ n + b → a ≤ b  
  +-lem {zero} le = le  
  +-lem {suc n'} (s≤s m≤n) = +-lem {n'} m≤n  