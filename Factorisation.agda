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

suc-inj : ∀ {x y} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

+inj : ∀ a x y → a + x ≡ a + y → x ≡ y
+inj zero x .x refl = refl
+inj (suc a) x y qq = +inj a x y (suc-inj qq)

composite-¬prime : ∀ n → Composite n → IsPrime n → ⊥
composite-¬prime .((2 + a) * (2 + b)) (composite a b) (not1 , pr) with pr (2 + b) (divides (2 + a) refl)
composite-¬prime ._ (composite a b) (not1 , pr) | inj₁ x with +inj (2 + b) 0 ((1 + a) * (2 + b)) (trans (+-comm (2 + b) 0) x)
... | ()
composite-¬prime ._ (composite a b) (not1 , pr) | inj₂ ()


data Facts : ℕ → Set where
  zero : Facts 0
  one : Facts 1
  fact : ∀ (p : Prime) m → Facts ((suc m) * proj₁ p)

*-∣-inj : ∀ m n q → q * m ∣ n → m ∣ n
*-∣-inj m .(q' * (q * m)) q (divides q' refl) = divides (q' * q) (sym (*-assoc q' q m))

qwe : ∀ a b c → a + b ≤ c → a ≤ c
qwe zero b c leq = z≤n
qwe (suc n) b zero ()
qwe (suc n) b (suc n') (s≤s m≤n) = s≤s (qwe n b n' m≤n)

Primes-Good-To : ℕ → List Prime → Set
Primes-Good-To top primes = ∀ (p : Prime) → proj₁ p < top → Any ((_≡_ (proj₁ p) ∘ proj₁)) primes

PrimesTo : ℕ → Set
PrimesTo top = Σ (List Prime) (Primes-Good-To top)


factor : (n : ℕ) → Facts n

factor' : (n m : ℕ) → m ≤′ n → Facts m
factor' m .m ≤′-refl = factor m
factor' (suc n) m (≤′-step m≤′n) = factor' n m m≤′n

found-prime : ∀ p primes → ¬ Any (λ p' → proj₁ p' ∣ p) primes → Primes-Good-To p primes → p ≤ 1 ⊎ IsPrime p
found-prime 0 _ _ _ = inj₁ z≤n
found-prime (suc p-1) primes none good = res where
  gg : IsPrime1 (suc p-1)
  res : (suc p-1) ≤ 1 ⊎ IsPrime (suc p-1)
  res with p-1 ≟ 0
  ... | yes eq rewrite eq = inj₁ (s≤s z≤n)
  ... | no neq = inj₂ ((λ x → neq (suc-inj x)) , gg)
  gg m divs with ≤⇒≤′ (∣⇒≤ divs)
  gg .(suc p-1) divs | ≤′-refl = inj₁ refl
  gg m divs | ≤′-step m≤′n with factor' p-1 m m≤′n
  gg .0 divs | ≤′-step m≤′n | zero with 0∣⇒≡0 divs
  ... | ()
  gg .1 divs | ≤′-step m≤′n | one = inj₂ refl
  gg .(suc m * proj₁ p) divs | ≤′-step m≤′n | fact p m = ⊥-elim (none (Data.List.Any.map (λ {x} → dd {x}) (good p ( s≤s (qwe (proj₁ p) (m * proj₁ p) p-1 (≤′⇒≤ m≤′n))  )))) where
   dd : ∀ {x : Prime} → proj₁ p ≡ proj₁ x → proj₁ x ∣ (suc p-1)
   dd {._ , _} refl = *-∣-inj (proj₁ p) (suc p-1) (suc m) divs

primesTo : (top : ℕ) → PrimesTo top

factor n with primesTo n
... | (primes , _) with any (λ p → proj₁ p ∣? n) primes
factor n | (primes , _) | yes found with satisfied found
factor .(0 * proj₁ p) | (primes , _) | yes found | p , divides 0 refl = zero
factor .(suc q * proj₁ p) | (primes , _) | yes found | p , divides (suc q) refl = fact p q
factor n | (primes , primes-good) | no ¬p with found-prime n primes ¬p primes-good
factor .0 | primes , primes-good | no ¬p | inj₁ z≤n = zero
factor .1 | primes , primes-good | no ¬p | inj₁ (s≤s z≤n) = one
... | inj₂ ispr = subst Facts (+-comm n 0) (fact (n , ispr) 0)


open import Function.Inverse
open import Function.Equality

extend : ∀ n → (PrimesTo n) → Dec (IsPrime n) → PrimesTo (suc n)
extend n (primes , good) dec = new dec ++ primes , gnl dec where

  new : Dec (IsPrime n) → List Prime
  new dec with dec
  ... | yes p = (n , p) ∷ []
  ... | no ¬p = []

  gnl : (dec : Dec (IsPrime n)) → Primes-Good-To (suc n) (new dec ++ primes)
  gnl dec p lss with ≤⇒≤′ lss
  gnl dec (._ , _) lss | ≤′-refl with dec
  gnl _ (.n , prf) lss | ≤′-refl | yes pp = here refl
  gnl _ (.n , prf) lss | ≤′-refl | no ¬p = ⊥-elim (¬p prf)
  gnl dec p lss | ≤′-step m≤′n = Inverse.to (++↔ {xs = new dec} {ys = primes}) ⟨$⟩ (inj₂ (good p (≤′⇒≤ m≤′n)))

zero-nonprime : ¬ IsPrime 0
zero-nonprime (_ , prm) with prm 2 (divides 0 refl)
zero-nonprime (_ , _) | inj₁ ()
zero-nonprime (_ , _) | inj₂ ()

one-nonprime : ¬ IsPrime 1
one-nonprime (neq , _) = ⊥-elim (neq refl)

prime≥2' : ∀ (p : Prime) → ∃ (λ p-2 → proj₁ p ≡ 2 + p-2)
prime≥2' (zero , proj₂) = ⊥-elim (zero-nonprime proj₂)
prime≥2' (suc zero , proj₂) = ⊥-elim (one-nonprime proj₂)
prime≥2' (suc (suc n) , proj₂) = n , refl

prime≥2 : ∀ (p : Prime) → proj₁ p ≥ 2
prime≥2 p with prime≥2' p
prime≥2 (.(suc (suc proj₁)) , pp) | proj₁ , refl = s≤s (s≤s z≤n)