------------------------------------------------------------------------
-- Generic clock interface.
------------------------------------------------------------------------

open import Data.Nat

module Event.Clock (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import Event.HappensBefore n Message
open import Data.Empty using (⊥-elim)
open import Data.Fin using(_≟_)
open import Data.Nat using (ℕ;_≤_;_≰_;_<_)
open import Data.Nat.Properties using (<⇒≱)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Relation.Binary.HeterogeneousEquality using (_≇_;refl;_≅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_;refl)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Nullary.Negation using (contraposition)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

ClockCompare = ∀ {pid pid′} {eid eid′} → Event pid eid → Event pid′ eid′ → Set

module _ (_≺_ : ClockCompare) where

   ⊏-Preserving : Set
   ⊏-Preserving = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                 e ⊏ e′ → e ≺ e′

   record ⊏-PreservingRules : Set where
     field
       ⊏-preserving-rule₁ : e ≺ send m e
       ⊏-preserving-rule₂ : e ≺ recv e′ e 
       ⊏-preserving-rule₃ : e ≺ recv e  e′
       ⊏-preserving-trans : e ⊏ e′ → e′ ⊏ e″ → e ≺ e″ 

   open ⊏-PreservingRules

   ⊏-PreservingRules-sufficient : ⊏-PreservingRules → ⊏-Preserving
   ⊏-PreservingRules-sufficient rules processOrder₁ = ⊏-preserving-rule₁ rules
   ⊏-PreservingRules-sufficient rules processOrder₂ = ⊏-preserving-rule₂ rules
   ⊏-PreservingRules-sufficient rules send⊏recv     = ⊏-preserving-rule₃ rules
   ⊏-PreservingRules-sufficient rules (trans x y)   = ⊏-preserving-trans rules x y
   
   ⊏-PreservingRules-necessary : ⊏-Preserving → ⊏-PreservingRules
   ⊏-preserving-rule₁ (⊏-PreservingRules-necessary x) = x processOrder₁
   ⊏-preserving-rule₂ (⊏-PreservingRules-necessary x) = x processOrder₂
   ⊏-preserving-rule₃ (⊏-PreservingRules-necessary x) = x send⊏recv
   ⊏-preserving-trans (⊏-PreservingRules-necessary x) y z = x (trans y z) 


   ⊏-Reflecting : Set
   ⊏-Reflecting = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                   e ≺ e′ → e ⊏ e′

   ⊏-ReflectingRule = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                   e ⊏̸ e′ → ¬ e ≺ e′

   ⊏-ReflectingRule-sufficient : ⊏-ReflectingRule → ⊏-Reflecting
   ⊏-ReflectingRule-sufficient x {e = e} {e′ = e′} y with ⊏-dec {e = e} {e′ = e′} 
   ... | inj₁ z = z
   ... | inj₂ z = ⊥-elim (x (¬⇒⊏̸ z) y)
   
   ⊏-ReflectingRules-necessary : ⊏-Reflecting → ⊏-ReflectingRule
   ⊏-ReflectingRules-necessary x y z = ⊏̸⇒¬ y (x z)

