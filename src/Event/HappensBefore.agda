------------------------------------------------------------------------
-- The happens-before relation.
------------------------------------------------------------------------

open import Data.Nat as ℕ

module Event.HappensBefore (n : ℕ) (Message : Set) where

open import Event.Execution n Message
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
open import Data.Nat.Properties as NatProp
open import Data.Product using (_×_; _,_;∃-syntax;Σ-syntax)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘′_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; inspect; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

private
  variable
    pid pid′ pid″ : ProcessId
    m  : Message
    e  : Event pid 
    e′ : Event pid′
    e″ : Event pid″

data _⊏_ : Event pid → Event pid′ → Set where
  processOrder₁ : e ⊏ send m e
  processOrder₂ : e ⊏ recv e′ e
  send⊏recv     : e ⊏ recv e e′
  trans         : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″

_∥_ : Event pid → Event pid′ → Set
_∥_ e e′ = ¬ e ⊏ e′ × ¬ e′ ⊏ e

data _prec_ : Event pid → Event pid → Set where
  send : e prec send m e
  recv : e prec recv e′ e

data _∈_ : Event pid → Event pid → Set where
  refl  : e ∈ e
  trans : e prec e′ → e′ ∈ e″ → e ∈ e″
  
Execution : Set
Execution = ∀ pid → Event pid

same-origin : Event pid → Event pid′ → Set
same-origin {pid} {pid′} e e′ = Σ[ exec ∈ Execution ] e ∈ exec pid × e′ ∈ exec pid′
  
eid[_] : Event pid → ℕ
eid[_] init        = zero
eid[_] (send _ e)  = suc (eid[ e ])
eid[_] (recv e e′) = suc (eid[ e′ ])

prec-eid-suc : e prec e′ → suc eid[ e ] ≡ eid[ e′ ]
prec-eid-suc send = refl
prec-eid-suc recv = refl

prec-eid : e prec e′ → eid[ e ] < eid[ e′ ]
prec-eid send = s≤s ≤-refl
prec-eid recv = s≤s ≤-refl

∈-eid : e ∈ e′ → eid[ e ] ≤ eid[ e′ ]
∈-eid refl         = ≤-refl
∈-eid (trans x y)  = <⇒≤ (<-transˡ (prec-eid x) (∈-eid y))

uniquely-identify-eid₁ : e prec e″ → e′ prec e″ → e ≡ e′
uniquely-identify-eid₁ send send = refl
uniquely-identify-eid₁ recv recv = refl

uniquely-identify-eid : e ∈ e″ → e′ ∈ e″ → eid[ e ] ≡ eid[ e′ ] → e ≡ e′
uniquely-identify-eid refl refl _ = refl
uniquely-identify-eid refl (trans x y) z = ⊥-elim (<⇒≢ (<-transˡ (prec-eid x) (∈-eid y)) (sym z))
uniquely-identify-eid (trans x y) refl z =  ⊥-elim (<⇒≢ (<-transˡ (prec-eid x) (∈-eid y)) z )
uniquely-identify-eid {e′ = e′} (trans {e′ = e₁} x y) (trans {e′ = e₂} z w) v = uniquely-identify-eid₁ x (subst  (e′ prec_) (uniquely-identify-eid w y s) z) 
  where
    s : eid[ e₂ ] ≡ eid[ e₁ ]
    s rewrite sym (prec-eid-suc x) | sym (prec-eid-suc z) = cong suc (sym v)


uniquely-identify : same-origin e e′ → pid[ e ] ≡ pid[ e′ ] → eid[ e ] ≡ eid[ e′ ] → e ≡ e′
uniquely-identify (_ , e∈ex , e′∈ex) _ eid≡ = uniquely-identify-eid e∈ex e′∈ex eid≡
------------------------------------------------------------------------
-- Properties about `_⊏_`, in particular, it's a strict partial order.

-- size : Event pid eid → ℕ
-- size init        = zero
-- size (send _ e)  = suc (size e)
-- size (recv e e′ _) = suc (size e + size e′)

-- ⊏⇒size< : e ⊏ e′ → size e < size e′
-- ⊏⇒size< processOrder₁ = s≤s ≤-refl
-- ⊏⇒size< processOrder₂ = s≤s (≤-stepsˡ _ ≤-refl)
-- ⊏⇒size< send⊏recv     = s≤s (≤-stepsʳ _ ≤-refl)
-- ⊏⇒size< (trans x y)   = ≤-trans (⊏⇒size< x) (<⇒≤ (⊏⇒size< y))

-- ⊏-irrefl : ¬ e ⊏ e
-- ⊏-irrefl x = 1+n≰n (⊏⇒size< x)

-- ⊏-trans : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″
-- ⊏-trans = trans

-- ⊏-asym : e ⊏ e′ → ¬ e′ ⊏ e
-- ⊏-asym x y = ⊥-elim (⊏-irrefl (⊏-trans x y))

-- ⊏-antisym : e ⊏ e′ → e′ ⊏ e → e ≅ e′
-- ⊏-antisym x y = ⊥-elim (⊏-asym x y)

-- ⊏-irrefl′ : e ≅ e′ → ¬ e ⊏ e′
-- ⊏-irrefl′ refl = ⊏-irrefl

-- ¬e⊏init : e′ ≡ init → ¬ e ⊏ e′
-- ¬e⊏init refl (trans x x₁) = ¬e⊏init refl x₁

-- eid<⇒⊏-locally : pid[ e ] ≡ pid[ e′ ] → eid[ e ] < eid[ e′ ] → e ⊏ e′
-- eid<⇒⊏-locally {_} {eid} {e} {_} {suc eid′} {send m e′} x y with <-cmp eid eid′
-- ... | tri< a _ _ = trans (eid<⇒⊏-locally x a) processOrder₁
-- ... | tri> _ _ c = ⊥-elim (1+n≰n (≤-trans y c))
-- ... | tri≈ _ b _ with uniquely-identify {e = e} {e′ = e′} x b
-- ... | refl = processOrder₁
-- eid<⇒⊏-locally {_} {eid} {e} {_} {suc eid′} {recv  _ e′} x y with <-cmp eid eid′
-- ... | tri< a _ _ = trans (eid<⇒⊏-locally x a) processOrder₂
-- ... | tri> _ _ c = ⊥-elim (1+n≰n (≤-trans y c))
-- ... | tri≈ _ b _ with uniquely-identify {e = e} {e′ = e′} x b
-- ... | refl = processOrder₂

-- ⊏⇒eid<-locally : pid[ e ] ≡ pid[ e′ ] → e ⊏ e′ → eid[ e ] < eid[ e′ ]
-- ⊏⇒eid<-locally {e = e} {e′ = e′} x y with <-cmp eid[ e ] eid[ e′ ]
-- ... | tri< a _ _ = a
-- ... | tri≈ _ b _ = ⊥-elim (⊏-irrefl′ (uniquely-identify x b) y)
-- ... | tri> _ _ c = ⊥-elim (⊏-asym y (eid<⇒⊏-locally (sym x) c ))

-- ⊏-tri-locally : pid[ e ] ≡ pid[ e′ ] → e ⊏ e′ ⊎ e ≅ e′ ⊎ e′ ⊏ e
-- ⊏-tri-locally {pid} {eid} {_} {pid} {eid′} {_} refl with <-cmp eid eid′
-- ... | tri< a _ _ = inj₁ (eid<⇒⊏-locally refl a)
-- ... | tri≈ _ b _ = inj₂ (inj₁ (uniquely-identify refl b))
-- ... | tri> _ _ c = inj₂ (inj₂ (eid<⇒⊏-locally refl c))

-- ⊏-inv₁ : e ⊏ send m e′ → e ≅ e′ ⊎ e ⊏ e′
-- ⊏-inv₁ processOrder₁ = inj₁ refl
-- ⊏-inv₁ (trans x y) with ⊏-inv₁ y
-- ... | inj₁ refl = inj₂ x
-- ... | inj₂ z    = inj₂ (trans x z)

-- ⊏-inv₂ : e ⊏ recv e′ e″ → (e ≅ e′ ⊎ e ⊏ e′) ⊎ (e ≅ e″ ⊎ e ⊏ e″)
-- ⊏-inv₂ processOrder₂ = inj₂ (inj₁ refl)
-- ⊏-inv₂ send⊏recv     = inj₁ (inj₁ refl)
-- ⊏-inv₂ (trans x y) with ⊏-inv₂ y
-- ... | inj₁ (inj₁ refl) = inj₁ (inj₂ x)
-- ... | inj₁ (inj₂ z)    = inj₁ (inj₂ (trans x z))
-- ... | inj₂ (inj₁ refl) = inj₂ (inj₂ x)
-- ... | inj₂ (inj₂ z)    = inj₂ (inj₂ (trans x z))

-- ⊏-dec : e ⊏ e′ ⊎ ¬ e ⊏ e′
-- ⊏-dec {e = e} {e′ = init} = inj₂ ((λ ()) ∘′ ⊏⇒size<)
-- ⊏-dec {e = e} {e′ = send _ e′} with ≅-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e′}
-- ... | inj₁ refl | _      = inj₁ processOrder₁
-- ... | inj₂ x    | inj₁ y = inj₁ (trans y processOrder₁)
-- ... | inj₂ x    | inj₂ y = inj₂ ([ x , y ]′ ∘′ ⊏-inv₁)
-- ⊏-dec {e = e} {e′ = recv e′ e″} with ≅-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e′} | ≅-dec {e = e} {e′ = e″} | ⊏-dec {e = e} {e′ = e″}
-- ... | inj₁ refl | _      | _         | _      = inj₁ send⊏recv
-- ... | _         | inj₁ y | _         | _      = inj₁ (trans y send⊏recv)
-- ... | _         | _      | inj₁ refl | _      = inj₁ processOrder₂
-- ... | _         | _      | _         | inj₁ w = inj₁ (trans w processOrder₂)
-- ... | inj₂ x    | inj₂ y | inj₂ z    | inj₂ w = inj₂ ([ [ x , y ]′ , [ z , w ]′ ]′ ∘′ ⊏-inv₂)

-- ------------------------------------------------------------------------
-- -- Defines `_⊏̸_`, the inductive version of the not-happens-before
-- -- relation, and shows it's equivalent to the negated version.

-- data _⊏̸_ : Event pid eid → Event pid′ eid′ → Set where
--   ⊏̸-eid  : pid[ e ] ≡ pid[ e′ ] → eid[ e′ ] ≤ eid[ e ] → e ⊏̸ e′
--   ⊏̸-init : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → e ⊏̸ e′
--   ⊏̸-send : pid[ e ] ≢ pid[ e′ ] → e ⊏̸ e′ → e ⊏̸ send m e′
--   ⊏̸-recv : pid[ e ] ≢ pid[ e′ ] → e ⊏̸ e′ → e ⊏̸ e″ → e ≇ e″ → e ⊏̸ recv e″ e′

-- ¬⇒⊏̸ : ¬ e ⊏ e′ → e ⊏̸ e′
-- ¬⇒⊏̸ {pid} {_} {_} {pid′} {_} {_} with pid Fin.≟ pid′
-- ... | yes x = ¬⇒⊏̸₁ x
--   where
--   ¬⇒⊏̸₁ : pid[ e ] ≡ pid[ e′ ] → ¬ e ⊏ e′ → e ⊏̸ e′
--   ¬⇒⊏̸₁ {pid} {eid} {e} {pid′} {eid′} {e′} x y with <-cmp eid eid′
--   ... | tri< a _ _  = ⊥-elim (y (eid<⇒⊏-locally x a))
--   ... | tri≈ _ b _  = ⊏̸-eid x (≤-reflexive (sym b))
--   ... | tri> _ _ c  = ⊏̸-eid x (<⇒≤ c)
-- ... | no  x = ¬⇒⊏̸₂ x
--   where
--   ¬⇒⊏̸₂ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → e ⊏̸ e′
--   ¬⇒⊏̸₂ {e = e} {e′ = init}       x y = ⊏̸-init x refl
--   ¬⇒⊏̸₂ {e = e} {e′ = send m e′}  x y with ⊏-dec {e = e} {e′ = e′}
--   ... | inj₁ z = ⊥-elim (y (trans z processOrder₁))
--   ... | inj₂ z = ⊏̸-send x (¬⇒⊏̸ z)
--   ¬⇒⊏̸₂ {e = e} {e′ = recv e″ e′} x y with ⊏-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e″} | ≅-dec {e = e} {e′ = e″}
--   ... | inj₁ z | _      | _         = ⊥-elim (y (trans z processOrder₂))
--   ... | _      | inj₁ w | _         = ⊥-elim (y (trans w send⊏recv))
--   ... | _      | _      | inj₁ refl = ⊥-elim (y send⊏recv)
--   ... | inj₂ z | inj₂ w | inj₂ u    = ⊏̸-recv x (¬⇒⊏̸ z) (¬⇒⊏̸ w) u

-- ⊏̸⇒¬ : e ⊏̸ e′ → ¬ e ⊏ e′
-- ⊏̸⇒¬ (⊏̸-eid  pid≡pid′ eid′≤eid)       = λ x → <-irrefl refl (<-transˡ (⊏⇒eid<-locally pid≡pid′ x) eid′≤eid)
-- ⊏̸⇒¬ (⊏̸-init pid≢pid′ refl)           = (λ ()) ∘′ ⊏⇒size<
-- ⊏̸⇒¬ (⊏̸-send pid≢pid′ e⊏̸e′)           = [ (λ { refl → pid≢pid′ refl}) , ⊏̸⇒¬ e⊏̸e′ ]′ ∘′ ⊏-inv₁
-- ⊏̸⇒¬ (⊏̸-recv pid≢pid′ e⊏̸e′ e⊏̸e″ e≇e″) = [ [ e≇e″ , ⊏̸⇒¬ e⊏̸e″ ]′ , [ (λ { refl → pid≢pid′ refl}) , ⊏̸⇒¬ e⊏̸e′ ]′ ]′ ∘′ ⊏-inv₂
