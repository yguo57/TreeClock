open import Data.Nat using (ℕ;zero;suc)

module Event.Execution (n : ℕ) (Message : Set) where

open import Data.Fin using (Fin)

ProcessId = Fin n

private
  variable
    pid pid′ pid″ : ProcessId
    m  : Message
    

data Event : ProcessId → Set where
  init : ∀ {pid} →
       Event pid
  send : ∀ {pid} →
       Message →
       Event  pid → Event pid 
  recv : ∀ {pid pid′} →
       (e′ : Event pid′) →
       (e : Event pid) →
       Event pid

pid[_] : Event pid → ProcessId
pid[_] {pid} e = pid
