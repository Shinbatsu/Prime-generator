open import Data.Maybe
open import Data.Empty
open import Data.Unit
open import Relation.Binary
module MRel {A : Set} (_<_ : A → A → Set) where
  _m<_ : Maybe A → Maybe A → Set
  _ m< nothing = ⊥
  nothing m< _ = ⊤
  just x m< just y = x < y

  trans : Transitive _<_ → Transitive _m<_
  trans tr {just _} {just _} {just _} mm1 mm2 = tr mm1 mm2
  trans tr {_} {_} {nothing} mm1 ()
  trans tr {nothing} {just _} {just _} mm1 mm2 = Data.Unit.tt
  trans tr {a} {nothing} () mm2
