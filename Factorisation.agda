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

