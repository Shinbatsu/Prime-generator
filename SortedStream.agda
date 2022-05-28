
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
  
open import Function

Bounded-> : ∀ {A : Set} → (_<_ : A → A → Set) → A → (A → A → Set)
Bounded-> _<_ max = λ a b → b < a × a < max

open import Induction.WellFounded

module WithTotalOrder (A : Set) (_<_ : A → A → Set) (order : IsStrictTotalOrder _≡_ _<_)
  (>-wf : ∀ max → Well-founded (Bounded-> _<_ max))
    where
  open IsStrictTotalOrder order


  module MR = MRel _<_
  open MR using (_m<_)
  mtrans : ∀ {a b c} → a m< b → b m< c → a m< c
  mtrans {a} {b} {c} = MR.trans trans {a} {b} {c}

  extend-isMinimal : ∀ {P : A → Set} x → {b : A} → 
     IsMinimal (Good P _<_ (just b)) _<_ x → ∀ {a} → None P _<_ a b → IsMinimal (Good P _<_ a) _<_ x
  extend-isMinimal x {b} mn {a} nn {y} good-y y<x with b <? y
  extend-isMinimal x mn nn {y} (py , a<y) y<x | yes b<y = mn {y} (py , b<y) y<x
  extend-isMinimal x mn nn {y} (py , a<y) y<x | no ¬p = nn a<y (λ z → mn (py , z) y<x) py

  m>-wf : ∀ max → Well-founded (Bounded-> _m<_ max)
  m>-wf nothing = λ _ → acc λ { x (_ , ()) }
  m>-wf (just max) = gogogo where
    ACC = Acc (Bounded-> _m<_ (just max))
    ACc = Acc (Bounded-> _<_ max)
    go : ∀ x → ACc x → ACC (just x)
    go x (acc accc) = acc (λ { nothing (() , _) ; (just y) lsss → go y (accc y lsss) })

    gogo : ∀ x → ACC (just x)
    gogo x = go x (>-wf max x)

    gogogo : ∀ x → ACC x
    gogogo nothing = acc λ { nothing (() , _) ; (just y) lsss → gogo y }
    gogogo (just x) = gogo x
