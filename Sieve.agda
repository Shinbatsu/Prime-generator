module Sieve where

open import Function
open import Function.Equivalence
open import Induction.WellFounded

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
