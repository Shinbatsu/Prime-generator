module Main where

open import IO
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Show
open import Data.Maybe
open import Data.Empty
open import Data.Unit
open import Coinduction
open import Multiples
open import SortedStream
open import Sieve
open import Data.Fin using (toℕ)

print : ℕ → IO ⊤
print n = putStrLn (show n)

printMults : ℕ → ℕ → IO ⊤
printMults n k = ♯ print (n * k) >> ♯ printMults n (suc k)

printAll : ∀ {P : ℕ → Set} {b : Maybe ℕ} → SortedStream _<_ P b → IO ⊥
printAll (minimum x _ _ ∷ taill) = ♯ print x >> ♯ printAll (♭ taill)

main = run (printAll all-primes)
