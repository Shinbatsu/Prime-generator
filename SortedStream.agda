
module SortedStream where

import MRel
open import Data.Maybe
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Coinduction
open import Relation.Binary hiding (Minimum)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)
open import Relation.Unary
open import Relation.Nullary
import Level

IsMinimal : ∀ {A : Set} → (P : Pred A Level.zero) (_<_ : A → A → Set) → Pred A Level.zero
IsMinimal P _<_ x = ∀ {y} → P y → ¬ y < x

record Minimum {A : Set} (P : Pred A Level.zero) (_<_ : A → A → Set) : Set where
 constructor minimum
 field
  value : A
  holds : P value
  isMin : IsMinimal P _<_ value

None : {A : Set} (P : Pred A Level.zero) (_<_ : A → A → Set) (lb : Maybe A) (ub : A) → Set
None P _<_ lb ub = let open MRel _<_ in ∀ {x} → lb m< just x → ¬ ub < x → ¬ P x

Good : ∀ {A : Set} (P : A → Set) (_<_ : A → A → Set) (bound : Maybe A) → A → Set
Good P _<_ bnd x = let open MRel _<_ in P x × bnd m< just x

record SortedStream {A : Set} (_<_ : A → A → Set) (P : A → Set) (b : Maybe A) : Set where
 inductive
 constructor _∷_
 field
  headd : Minimum (Good P _<_ b) _<_
  taill : ∞ (SortedStream _<_ P (just (Minimum.value headd)))
