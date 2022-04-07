open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_)

module TreeClock.TreeClockMaplessProp (n : ℕ) (Message : Set) where

open import TreeClock.TreeClockMapless n Message
open import Event.Event n Message
open import Event.HappensBefore n Message
open import Data.List using (List;[];_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using(Any;here;there)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″
 
data _childOf_ {K : Set} {V : Set} : MapTree K V → MapTree K V → Set where
  direct : ∀ {k : K} {v : V} {ts : List (MapTree K V)} → (t₁ : MapTree K V) → t₁ ∈ ts → t₁ childOf (node k v ts)
  trans : ∀{t₁ t₂ t₃} → t₁ childOf t₂ → t₂ childOf t₃  → t₁ childOf t₃

inc-inrrelev-child :  ∀{k v k′ v′ ts ts′} →  inc (node k′ v′ ts′) ≡ (node k v ts) → ts ≡ ts′
inc-inrrelev-child {ts = ts} {ts′ = .ts} refl = refl

inc-irrelev-childOf₁ : ∀ {t t′} → (t childOf t′) → (t childOf (inc t′))
inc-irrelev-childOf₁ (direct _ x) = direct _ x
inc-irrelev-childOf₁ (trans x y)  = trans x (inc-irrelev-childOf₁ y)

inc-irrelev-childOf₂ : ∀ {t t′} → (t childOf (inc t′)) → (t childOf t′)
inc-irrelev-childOf₂ {t′ = t′} x            with inc t′  | inspect inc t′ 
inc-irrelev-childOf₂ {t′ = node _ _ ts′} (direct _ x)    | _  | Eq.[ eq ] rewrite inc-inrrelev-child eq = direct _ x
inc-irrelev-childOf₂ {t′ = t′} (trans x y)               | _  | Eq.[ refl ] = trans x (inc-irrelev-childOf₂ y)

 -- premise incorrect due to transformation on the child tree,  use eid and pid to identify the event instead of the concrete event e

child⊏parent : treeClock[ e ] childOf treeClock[ e′ ] → e ⊏ e′
child⊏parent {e = e} {e′ = e′}   _                            with treeClock[ e′ ] | inspect treeClock[_] e′
child⊏parent {e = e} {e′ = init} (direct _ (here refl))         | _               | ()
child⊏parent {e = e} {e′ = send m e′} x                         | _               | Eq.[ refl ] = trans (child⊏parent (inc-irrelev-childOf₂  x )) processOrder₁
child⊏parent {e = e} {e′ = recv e″ e′₁} (direct _ (here refl))  | node x₁ x₂ .(treeClock[ e ] ∷ _) | w = {!!}
child⊏parent {e = e} {e′ = e′} (direct _ (there x))             | node x₁ x₂ .(_ ∷ _) | w  = {!!}
child⊏parent {e = e} {e′ = e′} (trans {t₂ = t₂} x y) | _ | Eq.[ eq ] = trans (child⊏parent x) (child⊏parent {!!})
