open import Data.Fin using (fromℕ<)
open import Data.Nat using (_≤_;s≤s;z≤n)
open import Data.Product using(_×_;_,_)
open import Data.List using ([];_∷_;[_])
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)

module TreeClockTest (Message : Set) (m₁ m₂ m₃ : Message)where

open import Event 4 Message
open import TreeClock 4 Message

p₀ p₁ p₂ p₃ : ProcessId 
p₀ = fromℕ< {m = 0}(s≤s z≤n)
p₁ = fromℕ< {m = 1} (s≤s (s≤s z≤n)) 
p₂ = fromℕ< {m = 2} (s≤s (s≤s (s≤s z≤n)))
p₃ = fromℕ< {m = 3} (s≤s (s≤s (s≤s (s≤s z≤n))))

ev₁₁ : Event p₀ 0
ev₁₁ = init

tree₁₁ : ClockTree
tree₁₁ = node p₀ (0 , 0) []

_ : treeClock[ ev₁₁ ] ≡ tree₁₁
_ = refl

ev₂₁ : Event p₁ 1
ev₂₁ = recv ev₁₁ init

test₁ :  treeClock[ ev₂₁ ] ≡
  node p₁ (1 , 0)
  (node p₀ (0 , 1) [] ∷ [])
test₁  = refl 

ev₂₂ : Event p₁ 2
ev₂₂ = send m₂ ev₂₁

ev₃₁ : Event p₂ 1
ev₃₁ = recv ev₂₁ init

ev₃₂ : Event p₂ 2
ev₃₂ = send m₃ ev₃₁

ev₄₁ : Event p₃ 1
ev₄₁ = recv ev₂₂ init

ev₄₂ : Event p₃ 2
ev₄₂ = recv ev₃₂ ev₄₁

test₃ : treeClock[ ev₄₂ ] ≡
  node p₃
  (2 , 0)
  (node p₂ (2 , 2) [] ∷
  node p₁ (2 , 1)
  (node p₀ (0 , 1) [] ∷ [])
  ∷ [])
test₃  = refl
