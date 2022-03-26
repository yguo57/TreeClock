open import Data.Fin using (fromℕ<)
open import Data.Nat using (_≤_;s≤s;z≤n)
open import Data.List using ([];_∷_;[_])
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)

module TreeClockTest (Message : Set) (m₁ m₂ m₃ m₄ m₅ : Message) where

open import Event 4 Message
open import TreeClock 4 Message

p₁ p₂ p₃ p₄ : ProcessId 
p₁ = fromℕ< {m = 0}(s≤s z≤n)
p₂ = fromℕ< {m = 1} (s≤s (s≤s z≤n)) 
p₃ = fromℕ< {m = 2} (s≤s (s≤s (s≤s z≤n)))
p₄ = fromℕ< {m = 3} (s≤s (s≤s (s≤s (s≤s z≤n))))

ev₁₁ : Event p₁ 1
ev₁₁ = send m₁ init

tree₁₁ : ClockTree
tree₁₁ = node p₁ 1 []

_ : treeClock[ ev₁₁ ] ≡ tree₁₁
_ = refl

ev₂₁ : Event p₂ 2
ev₂₁ = send m₂ (recv ev₁₁ init)

tree₂₁ : ClockTree
tree₂₁ = inc (node p₂ 0 [ tree₁₁ ])

test₁ :  treeClock[ ev₂₁ ] ≡ tree₂₁
test₁  = refl 

ev₂₂ : Event p₂ 3
ev₂₂ = send m₃ ev₂₁

ev₃₁ : Event p₃ 2
ev₃₁ = send m₄ (recv ev₂₁ init)

ev₃₂ : Event p₃ 3
ev₃₂ = send m₅ ev₃₁

ev₄₁ : Event p₄ 1
ev₄₁ = recv ev₂₂ init

ev₄₂ : Event p₄ 2
ev₄₂ = recv ev₃₂ ev₄₁

test₃ : treeClock[ ev₄₂ ] ≡ node p₄ 0
 (node p₃ 2 [] ∷
 node p₂ 2 (node p₁ 1 [] ∷ [])
 ∷ [])
test₃  = refl
