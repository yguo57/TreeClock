module Event.FreeMonad where

open import Data.Product

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

data Free :  (Set → Set) → Set → Set where
  pure : {f : Set → Set}{a : Set} → a  → Free f a
  free : {f : Set → Set}{a : Set} → (Free f a) → Free f a

data Event {M : Set} {V : Set} (f : V → V) (s : V → M ) (r : V → M → V) : V → Set where
  init : (v : V) → Event f s r v
  send : ∀{v} → Event f s r v →  Event f s r (f v)
  recv : ∀ {v v′}{e : Event f s r v′} →  Event f s r v → (e′ : Event f s r (f v′)) → {send e ≡ e′}  →  Event f s r (r v (s v′))

