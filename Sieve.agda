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

open import Function
open import Function.Equivalence
open import Induction.WellFounded

open import Relation.Binary hiding (Minimum)
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import SortedStream

import Level
import MRel
import PrimesInfinite
open import Multiples
open import Factorisation

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



 isRetainedAfterSieve-step : ∀ { n } → (p : Minimum (IsPrime'> n) _<_) 
   → ∀ { m }
   → IsRetainedAfterSieve≤ n m
   → let pv = Minimum.value p in
     ¬ pv ∣ m
   → IsRetainedAfterSieve≤ pv m
 isRetainedAfterSieve-step {n} (minimum pv _ isMin) {m} (m>1 , no-divs) ¬div = m>1 , no' where
   no' : (∀ x → x ≤ pv → IsPrime x → ¬ x ∣ m)
   no' x x≤p isP x∣m with x ≟ pv
   no' .pv x≤p isP x∣m | yes PropEq.refl = ¬div x∣m
   ... | no neq = no-divs x x≤n isP x∣m where
    x≤n : x ≤ n
    x≤n with x ≤? n
    x≤n | yes x≤n = x≤n
    x≤n | no ¬x≤n = ⊥-elim (isMin {x} (prime⇒prime' isP , ≰⇒> ¬x≤n) (z' x≤p neq))

 isRetainedAfterSieve-step-rev : ∀ { n } → (p : Minimum (IsPrime'> n) _<_) 
   → ∀ { m }
   → let pv = Minimum.value p in
   IsRetainedAfterSieve≤ pv m
   → IsRetainedAfterSieve≤ n m × ¬ pv ∣ m
 isRetainedAfterSieve-step-rev {n} (minimum p (p-prime , n<p) isMin) {m} (m>1 , ret) = (m>1 , prevRet) , ¬div where

   prevRet : ∀ x → x ≤ n → IsPrime x → ¬ x ∣ m
   prevRet x x≤n = ret x (≤O.trans x≤n (≤O.trans (n≤m+n 1 n) n<p))

   ¬div : ¬ p ∣ m
   ¬div p∣m = ret p (≤O.reflexive PropEq.refl) (prime'⇒prime p-prime) p∣m

wf : ∀ max → Well-founded (λ a b → a > b × a < max)
wf = qqq where


 data _≤''_ : ℕ → ℕ → Set where
  ≤''-refl : ∀ {m} →                         m ≤'' m
  ≤''-step : ∀ {m n} (m≤′n : m ≤'' n) → pred m ≤'' n

 <'⇒≤′ : ∀ a b → a <′ b → a ≤′ b
 <'⇒≤′ a .(suc a) ≤′-refl = ≤′-step ≤′-refl
 <'⇒≤′ a .(suc n) (≤′-step {n} m≤′n) = ≤′-step (<'⇒≤′ a n m≤′n)

 s' : ∀ a b → a ≤'' b → a ≤'' suc b
 s' .b b ≤''-refl = ≤''-step ≤''-refl
 s' .0 b (≤''-step {zero} m≤′n) = s' zero b m≤′n
 s' .n b (≤''-step {suc n} m≤′n) = ≤''-step (s' (suc n) b m≤′n)

 ≤''→≤′ : ∀ a b → a ≤'' b → a ≤′ b
 ≤''→≤′ .b b ≤''-refl = ≤′-refl
 ≤''→≤′ .0 b (≤''-step {zero} m≤′n) = ≤''→≤′ zero b m≤′n
 ≤''→≤′ .n b (≤''-step {suc n} m≤′n) with ≤''→≤′ (suc n) b m≤′n
 ... | rec = <'⇒≤′ n b rec

 ≤′→≤'' : ∀ a b → a ≤′ b → a ≤'' b
 ≤′→≤'' .b b ≤′-refl = ≤''-refl
 ≤′→≤'' a .(suc n) (≤′-step {n} m≤′n) with ≤′→≤'' a n m≤′n
 ... | rec = s' a n rec

 lemm : ∀ a b → a > pred b → a ≢ b → a > b
 lemm a zero gt neq = gt
 lemm a (suc n) gt neq with compare a (suc n)
 lemm a (suc n) gt neq | tri< a' ¬b ¬c = ⊥-elim (irrefl PropEq.refl (Relation.Binary.DecTotalOrder.trans Data.Nat.Properties.≤-decTotalOrder a' gt))
 lemm a (suc n) gt neq | tri≈ ¬a b ¬c = ⊥-elim (neq b)
 lemm a (suc n) gt neq | tri> ¬a ¬b c = c


 z'' : ∀ max x → x ≤'' max → Acc (λ a b → a > b × a < max) x
 z'' max .max ≤''-refl = acc (λ { y (max<y , y<max) → ⊥-elim (irrefl PropEq.refl (trans max<y y<max)) })
 z'' max .(pred m) (≤''-step {m} m≤′n) with z'' max m m≤′n
 ... | acc rec = acc go where
  go : ∀ y → (y > pred m × y < max) → Acc (λ a b → a > b × a < max) y
  go y (y>m , y<max) with y ≟ m
  go .m (y>m , y<max) | yes PropEq.refl = acc rec
  ... | no neq = rec y (lemm y m y>m neq , y<max)

 qqq : ∀ max x → Acc (λ a b → a > b × a < max) x
 qqq max x with x ≤? max
 ... | yes x≤max = z'' max x ( ≤′→≤'' _ _ (Data.Nat.Properties.≤⇒≤′ x≤max))
 ... | no x>max = acc  (λ { y (x<y , y<max) →  ⊥-elim (x>max (Data.Nat.Properties.≤′⇒≤ (<'⇒≤′ _ _ (Data.Nat.Properties.≤⇒≤′ (trans x<y y<max))))) })

abstract
 small-not-retained : ∀ {n} {x} → IsRetainedAfterSieve≤ n x → x > n
 small-not-retained {n} {x} (x>1 , ret) with factor x
 small-not-retained (() , ret) | zero
 small-not-retained (s≤s () , ret) | one
 small-not-retained (x>1 , ret) | fact (p , p-prime) m = ≰⇒> (λ x≤n → ret p (≤O.trans (≤O.trans (≤O.reflexive (+-comm 0 p)) ((≤O.reflexive (PropEq.refl {x = 1}) +-mono (z≤n {m})) *-mono  ≤O.reflexive {p} PropEq.refl)) x≤n) p-prime (divides (suc m) PropEq.refl))

ho' : ∀ {n} → Minimum (λ x → IsRetainedAfterSieve≤ n x × ⊤) _<_ → Minimum (IsPrime'> n) _<_
ho' {n} (minimum p ((p>1 , isRet) , _) isMin) = minimum p (isPrime , p>n) isMin' where

  p≢1 : ¬ p ≡ 1
  p≢1 p≡1 = irrefl (PropEq.sym p≡1) p>1

  isMin' : IsMinimal (IsPrime'> n) _<_ p
  isMin' {q} ((q>1 , q-prime) , n<q) = isMin {q} ((q>1 , gg) , record {}) where
   gg : ∀ x → x ≤ n → IsPrime x → ¬ x ∣ q
   gg p' p'≤n = q-prime p' (≤O.trans (s≤s p'≤n) n<q)

  isPrime : IsPrime' p
  isPrime = p>1 , (λ m m<p mp → isRet m (≮⇒≥ (λ n<m → isMin' {m} (prime⇒prime' mp , n<m) m<p)) mp)

  p>n : p > n
  p>n = small-not-retained (p>1 , isRet)


sieve-step : ∀ {n} → Sifted≤ n → Σ (Minimum (IsPrime'> n) _<_) (λ pmin → Sifted≤ (Minimum.value pmin))
sieve-step {n} (headd ∷ taill) = p , substExhaustiveStream to from (subtract {b = nothing} (headd ∷ taill) (multiples pv pv>0) infinite) where
  pv : ℕ
  pv = Minimum.value headd

  p : Minimum (IsPrime'> n) _<_
  p = ho' headd

  pv>0 : pv > 0
  pv>0 with pv | proj₁ (proj₁ (Minimum.holds p))
  pv>0 | .(suc n') | s≤s {.1} {n'} m≤n = s≤s z≤n

  to : ∀ {x} → IsRetainedAfterSieve≤ n x × ¬ pv ∣ x → IsRetainedAfterSieve≤ pv x
  to {x} (ret , ord) = isRetainedAfterSieve-step p ret ord

  from : ∀ {x} → IsRetainedAfterSieve≤ pv x → IsRetainedAfterSieve≤ n x × ¬ pv ∣ x
  from x = isRetainedAfterSieve-step-rev p x

  open MRel _<_

  infinite' : ∀ n' → ∃ (λ m → n' < m × IsRetainedAfterSieve≤ n m × ¬ pv ∣ m)
  infinite' n = case PrimesInfinite.infinite (1 + pv + n) of λ where
    (m , 1+pv+n<m , good) → m , (≤O.trans (s≤s (n≤m+n (1 + pv) n)) 1+pv+n<m , from (≤O.trans (m≤m+n 2 (pv + n)) 1+pv+n<m , λ {x x≤pv → good x (≤O.trans x≤pv (≤O.trans (m≤m+n pv n) (n≤m+n 1 (pv + n)))) } ))

  infinite : ∀ n' → ∃ (λ m → n' m< just m × IsRetainedAfterSieve≤ n m × ¬ pv ∣ m)
  infinite nothing = case infinite' 0 of λ where
   (m , _ , res) → m , record {} , res
  infinite (just n) = infinite' n

AllPrimes = SortedStream _<_ IsPrime' (just 0)

abstract
 sieve-step-abs : ∀ {n} → Sifted≤ n → Σ (Minimum (IsPrime'> n) _<_) (λ pmin → Sifted≤ (Minimum.value pmin))
 sieve-step-abs = sieve-step


go-primes : ∀ {n} → Sifted≤ n → SortedStream _<_ IsPrime' (just n)
go-primes sifted with sieve-step-abs sifted
go-primes sifted | prime , sifted' = prime ∷ (♯ go-primes sifted')

seed : Sifted≤ 0
seed = gono where

  stupid : ∀ {n} x → x ≤ 0 → IsPrime x → ¬ x ∣ n
  stupid .0 z≤n qq x1 = zero-nonprime qq
  
  go : ∀ n-1 → SortedStream _<_ (IsRetainedAfterSieve≤ 0) (just (suc n-1))
  go n-1 = (minimum (suc (suc n-1)) good minimal) ∷ ♯ go (suc n-1) where

    n = suc n-1
    Good' = λ y → IsRetainedAfterSieve≤ 0 y × y > n

    good : Good' (suc n)
    good = (s≤s (s≤s z≤n) , stupid) , (≤O.reflexive PropEq.refl)
 
    minimal : ∀ {y} → Good' y → ¬ y < suc n
    minimal (proj₁ , n<y) (s≤s y<1+n) = <O.irrefl PropEq.refl (≤O.trans n<y  y<1+n)

  gono : SortedStream _<_ (IsRetainedAfterSieve≤ 0) nothing
  gono = (minimum 2 (((s≤s (s≤s z≤n)) , stupid) , Data.Unit.tt) minimal) ∷ ♯ go 1 where
   Good' = λ y → IsRetainedAfterSieve≤ 0 y × ⊤

   minimal : ∀ {y} → Good' y → ¬ y < 2
   minimal ((s≤s (s≤s m≤n) , proj₂) , proj₂') (s≤s (s≤s ()))

all-primes : SortedStream _<_ IsPrime' (just 0)
all-primes = go-primes seed
