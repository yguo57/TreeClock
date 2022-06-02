open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_)

module TC-VC-equiv (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import TreeClock.TreeClock n Message
open import TreeClock.MapTree
open import VectorClockFunctional n Message

open import Data.Fin as Fin
open import Data.List using ([];_∷_)
open import Data.Product using (_,_)
open import Data.Vec.Functional as Vector hiding (init)
open import Data.Vec.Functional.Properties as VectorProp
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_;refl)
open import Relation.Nullary using (yes; no)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″
    
tc-vc-equiv : ∀ i → vc[ e ] i ≡ lookupClk i treeClock[ e ]
tc-vc-equiv {e = e}         i with i Fin.≟ pid[ e ] | treeClock[ e ]
tc-vc-equiv {e = init}      i | yes _               | node k _ _ = {!!}
tc-vc-equiv {e = init}      i | no  _               | _  = {!!}
tc-vc-equiv {e = send _ e}  i | _                   | _  = {!!}
tc-vc-equiv {e = recv e e₁} i | _                   | _  = {!!}

