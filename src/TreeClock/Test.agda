open import Data.Fin using (fromℕ<)
open import Data.Nat using (_≤_;s≤s;z≤n)
open import Data.Product using(_×_;_,_)
open import Data.List using ([];_∷_;[_])
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)

module TreeClock.Test (Message : Set) (m₁ m₂ m₃ : Message)where

open import Event.Event 4 Message
open import TreeClock.TreeClock 4 Message

p₀ p₁ p₂ p₃ : ProcessId 
p₀ = fromℕ< {m = 0}(s≤s z≤n)
p₁ = fromℕ< {m = 1} (s≤s (s≤s z≤n)) 
p₂ = fromℕ< {m = 2} (s≤s (s≤s (s≤s z≤n)))
p₃ = fromℕ< {m = 3} (s≤s (s≤s (s≤s (s≤s z≤n))))

ev₀₀ : Event p₀ 0
ev₀₀ = init

_ : treeClock[ ev₀₀ ] ≡ node p₀ (0 , 0) []
_ = refl

ev₁₁ : Event p₁ 1
ev₁₁ = recv ev₀₀ init

_ :  treeClock[ ev₁₁ ] ≡
  node p₁ (1 , 0)
  (node p₀ (0 , 1) [] ∷ [])
_  = refl 

ev₁₂ : Event p₁ 2
ev₁₂ = send m₂ ev₁₁

ev₂₁ : Event p₂ 1
ev₂₁ = recv ev₁₁ init

ev₂₂ : Event p₂ 2
ev₂₂ = send m₃ ev₂₁

ev₃₁ : Event p₃ 1
ev₃₁ = recv ev₁₂ init

ev₃₂ : Event p₃ 2
ev₃₂ = recv ev₂₂ ev₃₁

_ : treeClock[ ev₃₂ ] ≡
  node p₃
  (2 , 0)
  (node p₂ (2 , 2) [] ∷
  node p₁ (2 , 1)
  (node p₀ (0 , 1) [] ∷ [])
  ∷ [])
_  = refl

tree₁ : ClockTree
tree₁ = {!!}
