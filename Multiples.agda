module Multiples where

open import Data.Nat
open import Data.Product
open import Data.Maybe

getBound : ℕ → ℕ → Maybe ℕ  
getBound _ zero = nothing  
getBound n (suc k) = just (k * n)  