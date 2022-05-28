
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


  Step : (P₁ P₂ : A → Set) → (mx : A) → (n : Maybe A) → Set
  Step P₁ P₂ mx n = 
    n m< just mx
    → (asbs : SortedStream _<_ P₁ n × SortedStream _<_ P₂ n)
    → Σ (Minimum (λ y → (P₁ y × ¬ P₂ y) × n m< just y) _<_) (λ mn → let x = Minimum.value mn in SortedStream {A} _<_ P₁ (just x) × SortedStream {A} _<_ P₂ (just x))

  subtract-step : 
    ∀ {P₁ : A → Set} {P₂ : A → Set} {n : Maybe A}
    → (mx : A)
    → (P₁ mx × ¬ P₂ mx)
    → Step P₁ P₂ mx n
  subtract-step {P₁} {P₂} {n} mx (p₁x , ¬p₂x) = All.wfRec (m>-wf (just mx)) _ (Step P₁ P₂ mx) go'' n where 

    _>_ = Bounded-> _m<_ (just mx)

    trans'' : ∀ {a b c} → ¬ b < a → b < c → a < c
    trans'' {a} {b} {c} a≤b b<c with compare a c
    ... | tri< y _ _  = y
    trans'' a≤b b<c | tri≈ ¬a PropEq.refl ¬c = ⊥-elim (a≤b b<c)
    ... | tri> _ _ gt = ⊥-elim (a≤b (trans b<c gt))

    go' : ∀ n
     → (as : SortedStream _<_ P₁ n)
     → (bs : SortedStream _<_ P₂ n)
     → ∃ ((((_m<_ n) ∩ (SortedStream {A} _<_ P₁ ∩ SortedStream {A} _<_ P₂)) ∘ just) ∩ (let PP = P₁ ∩ (¬_ ∘ P₂) in (PP ∩ IsMinimal (Good PP _<_ n) _<_) ∪ None PP _<_ n))
    go' n (minimum a (p₁a , n<a) a-minimal ∷ as) (minimum b (p₂b , n<b) b-minimal ∷ bs) with compare a b
    ... | tri< a<b _ _ = a , ((n<a , (♭ as , minimum b (p₂b , a<b) (λ { {y} (p₂y , a<y) → b-minimal (p₂y , mtrans {n} {just a} {just y} n<a a<y) }) ∷ bs)) , inj₁ ((p₁a , (λ p₂a → b-minimal (p₂a , n<a) a<b)) , λ { {y} ((p₁y , ¬p₂y) , n<y) y<a → a-minimal {y} (p₁y , n<y) y<a }))
    go' n (minimum a (p₁a , n<a) a-minimal ∷ as) (minimum .a (p₂b , n<b) b-minimal ∷ bs) | tri≈ _ PropEq.refl _ = a , (n<a , (♭ as , ♭ bs)) , inj₂ none where
     none : None (λ q → P₁ q × ¬ P₂ q) _<_ n a
     none {y} n<y a<y (p₁y , _) with compare y a
     ... | tri< y<a _ _ = a-minimal {y} (p₁y , n<y)  y<a
     none n<y a<y (p₁y , ¬p₂y) | tri≈ ¬a PropEq.refl ¬c = ⊥-elim (¬p₂y p₂b)
     ... | tri> _ _ y>a = ⊥-elim (a<y y>a)
    ... | tri> _ _ b<a = b , (n<b , minimum a (p₁a , b<a) (λ { {y} (p₁y , b<y) y<a → a-minimal {y} (p₁y , mtrans {n} {just b} {just y} n<b b<y) y<a }) ∷ as , ♭ bs) , inj₂ none where
     none : None (λ q → P₁ q × ¬ P₂ q) _<_ n b
     none {y} n<y ¬b<y (p₁p , ¬p₂y) = a-minimal (p₁p , n<y) (trans'' ¬b<y b<a)

    go'' : ∀ n → (rec : ∀ n' → n' > n → Step P₁ P₂ mx n') →  Step P₁ P₂ mx n
    go'' n rec n<mx (as , bs) with go' n as bs
    go'' n rec n<mx (as , bs) | n' , (n<n' , asbs') , inj₁ (n'-good , n'-minimal) = (minimum n' (n'-good , n<n') n'-minimal) , asbs'
    go'' n rec n<mx (as , bs) | n' , (n<n' , asbs') , inj₂ none with rec (just n') (n<n' , n'<mx) n'<mx asbs' where
      n'<mx : n' < mx
      n'<mx with n' <? mx
      n'<mx | yes n'<mx = n'<mx
      n'<mx | no n< = ⊥-elim (none n<mx n< (p₁x , ¬p₂x))
    ... | minimum r (p₁¬p₂r , n'<r) r-minimal , asbsr = minimum r (p₁¬p₂r , mtrans {n} {just n'} {just r} n<n' n'<r) (extend-isMinimal r {n'} r-minimal {n} none) , asbsr

  subtract : 
    {P₁ : A → Set} {P₂ : A → Set} {b : Maybe A}
    → SortedStream _<_ P₁ b
    → SortedStream _<_ P₂ b
    → (∀ n → ∃ (λ m → n m< just m × P₁ m × ¬ P₂ m))
    → SortedStream {A} _<_ (λ x → P₁ x × ¬ P₂ x) b
  subtract {b = b} str₁ str₂ good with good b
  ... | (m , b<m , gm) with subtract-step m gm b<m (str₁ , str₂)
  ... | x , r-str₁ , r-str₂ = x ∷ ♯ subtract r-str₁ r-str₂ good


