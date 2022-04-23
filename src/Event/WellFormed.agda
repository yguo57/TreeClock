open import Data.Nat using (ℕ;zero;suc)

module Event.WellFormed (n : ℕ) (Message : Set) where

open import Event.Execution n Message
open import Event.HappensBefore n Message

private
  variable
    pid pid′ pid″ : ProcessId
    m  : Message
    e  : Event pid 
    e′ : Event pid′
    e″ : Event pid″
    
data Wellformed : Event pid  → Set where
  wf-init : Wellformed (init {pid})
  wf-send : Wellformed e →
            Wellformed (send m e)
  wf-recv : Wellformed e →
            Wellformed e′ →
            same-origin e e′ →
             e ∥ e′ → 
            Wellformed (recv e e′)

