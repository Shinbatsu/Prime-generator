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