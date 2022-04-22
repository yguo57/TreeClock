open import Data.Nat using (ℕ;zero;suc)

module Event.Execution (n : ℕ) (Message : Set) where

open import Data.Product using (∃-syntax; _×_;Σ-syntax)
open import Data.Fin using (Fin)



ProcessId = Fin n
LocalEventId = ℕ 

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    

mutual

  Execution : Set
  Execution = ∀ pid → Event pid
  
  data Event : ProcessId → Set where
    init : ∀ {pid} →
         Event pid
    send : ∀ {pid} →
         Message →
         Event  pid → Event pid 
    recv : ∀ {pid pid′} →
         (e′ : Event pid′) →
         (e : Event pid) →
         same-origin e′ e  → 
         Event pid

  data _∈_ : Event pid → Event pid′ → Set where
    send∈ : ∀ {m pid} (e : Event pid) →
            e ∈ send m e
    recv∈ : ∀ {pid pid′} →
            (e′ : Event pid′) →
            (e : Event pid) →
            (s : same-origin e′ e) →
            e ∈ recv e′ e  s

  same-origin : Event pid → Event pid′ → Set
  same-origin {pid′} {pid} e′ e = Σ[ exec ∈ Execution ] e′ ∈ exec pid′ × e ∈ exec pid
         
