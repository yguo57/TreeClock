open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_;_<ᵇ_)

module TreeClock.Properties (n : ℕ) (Message : Set) where

open import TreeClock.TreeClock n Message
open import Event.Event n Message
open import TreeClock.MapTree ProcessId Value as ClockTree
open ClockTree.MapTree
open import Event.HappensBefore n Message
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (_≟_;suc)
open import Data.List using (List;[];_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using(Any;here;there)
open import Data.Maybe.Base using (nothing;just;boolToMaybe)
open import Data.Product using (_×_ ; _,_;Σ-syntax;proj₁;proj₂;uncurry′)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst;cong;sym) renaming (trans to transitive)
open import Relation.Binary.HeterogeneousEquality as Hetero using (_≅_)
open import Relation.Nullary using (yes; no; does;¬_)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

rootPid : ClockTree → ProcessId
rootPid (node pid _  _) = pid

rootClk : ClockTree → ℕ
rootClk (node _ (clk , _)  _) = clk

rootAclk : ClockTree → ℕ
rootAclk (node _ ( _ , aclk )  _) = aclk

postulate
  rootClk∘inc≡suc∘rootClk : ∀ t → rootClk (inc t) ≡ suc (rootClk t)
  getUpdatedNodesJoin-fix-rootClk : ∀ t₁ t₂ {t₁′} → getUpdatedNodesJoin t₁ t₂ ≡ just t₁′ → rootClk t₁′ ≡ rootClk t₁
  detachNodes-fix-rootClk : ∀ t₁ t₂ {t₂′} → detachNodes t₁ t₂ ≡ just t₂′ → rootClk t₂′ ≡ rootClk t₂
  pushChild-fix-rootClk : ∀ t₁ t₂ → rootClk (pushChild t₁ t₂)  ≡ rootClk t₂
                                                                                      
rootClk∘join≡suc∘rootClk  : ∀ t t′ →  rootClk (join t t′) ≡ suc (rootClk t′)
rootClk∘join≡suc∘rootClk t₁@(node pid (clk , _) _) t₂@(node pid′ (clk′ , _) _)
  with getUpdatedNodesJoin t₁ t₂  | inspect (getUpdatedNodesJoin t₁) t₂
... | nothing  | _  rewrite rootClk∘inc≡suc∘rootClk t₁  = cong suc refl
... | just t₁′ | Eq.[ eq ] with detachNodes t₁′ t₂ | inspect (detachNodes t₁′) t₂
...                         | just t₂′ | Eq.[ eq ] rewrite pushChild-fix-rootClk t₁′ (inc t₂′) | rootClk∘inc≡suc∘rootClk t₂′ | detachNodes-fix-rootClk t₁′ t₂ eq = cong suc refl 
...                         | nothing  | _ rewrite rootClk∘inc≡suc∘rootClk t₁′ = cong suc {!!}

eid≡rootClk : eid[ e ] ≡ rootClk treeClock[ e ]
eid≡rootClk {_} {zero} {e = init} = refl
eid≡rootClk {_} {(suc _)} {e = send m e}
  with treeClock[ e ] | inspect (treeClock[_]) e
... | (node _ (clk , _)  _) | Eq.[ eq ] = cong suc (transitive (eid≡rootClk {e = e}) (cong rootClk eq))
eid≡rootClk  {_} {suc _} {e = recv e e′} rewrite rootClk∘join≡suc∘rootClk treeClock[ e ] treeClock[ e′ ] = cong suc (eid≡rootClk {e = e′} )

_root≡_ : ClockTree → ClockTree → Set
_root≡_  t t′ = rootPid t ≡ rootPid t′ × rootClk t ≡ rootClk t′

_root∈_ : MapTree → List MapTree → Set 
_root∈_  t ts = Any (t  root≡_) ts

postulate
  join-attach-head : ∀ {k v ts t t′ t″} →  join t t′ ≡ node k v (t″ ∷ ts) → t root≡ t″
  join-tail-no-new-node : ∀ {k v ts t₁ t₂ t₃} →  join t₁ t₂ ≡ node k v (t₃ ∷ ts) → ∀{t₄} → t₄ root∈ ts → t₄ root∈ (children t₂)
  pid≡rootPid : pid[ e ] ≡ rootPid treeClock[ e ]
  
root≡-trans : ∀ {t t′ t″} → t root≡ t′ → t′ root≡ t″ → t root≡ t″
root≡-trans (a , b) (c , d) =  transitive a c , transitive b d

root≡-sym : ∀ {t t′} → t root≡ t′ → t′ root≡ t
root≡-sym (a , b) =  sym a , sym b

root≡⇒Pid≡×Clk≡ : treeClock[ e ] root≡ treeClock[ e′ ] → pid[ e ] ≡ pid[ e′ ] × eid[ e ] ≡ eid[ e′ ]
root≡⇒Pid≡×Clk≡ {e = e} {e′ = e′} (a , b) = transitive (transitive (pid≡rootPid {e = e}) a) (sym (pid≡rootPid {e = e′}) ) , transitive (transitive (eid≡rootClk {e = e})  b) (sym (eid≡rootClk {e = e′}))

data _TC-childOf_ : Event pid eid → Event pid′ eid′ → Set where
  immed : treeClock[ e ] root∈ (children treeClock[ e′ ]) → e TC-childOf e′
  recur : e TC-childOf e′ → e′ TC-childOf e″ → e TC-childOf e″ 

inc-irrelev-child :  ∀ t →  children (inc t) ≡ children t
inc-irrelev-child _ = refl

inc-irrelev-childOf₁ : ∀ t t′ → t root∈ (children t′) → t root∈ (children (inc t′))
inc-irrelev-childOf₁ t t′ x = subst (t root∈_) (sym (inc-irrelev-child t′)) x 

inc-irrelev-childOf₂ :  ∀ t t′ → t root∈ (children (inc t′)) → t root∈ (children t′)
inc-irrelev-childOf₂ t t′ x = subst (t root∈_ )  (inc-irrelev-child  t′) x 

treeOrder₁ : ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
             treeClock[ e ] root∈ (children treeClock[ e′ ]) → e ⊏ e′
treeOrder₁ {e = e} {e′ = e′} x  with treeClock[ e ] | treeClock[ e′ ] | inspect treeClock[_] e | inspect treeClock[_] e′
treeOrder₁ {e = e} {e′ = init} ()               | _ | node _ _ [] | _ | _
treeOrder₁ {e = e} {e′ = send _ e′} x           | t | _ | Eq.[ refl ] | Eq.[ eq ]  = trans y processOrder₁
  where
    y : e ⊏ e′
    y = treeOrder₁ {e = e} (inc-irrelev-childOf₂ t treeClock[ e′ ] (subst (λ t → treeClock[ e ] root∈ (children t)) (sym eq) x ))
treeOrder₁ {e = e} {e′ = recv e′ _} (here x)   | _ | node _ _ (t′ ∷ _) | Eq.[ eq ] | Eq.[ eq₂ ] = helper (uncurry′ uniquely-identify (root≡⇒Pid≡×Clk≡ {e = e′} {e′ = e} w))
  where
      helper : e′ ≅ e → e ⊏ recv e′ e″
      helper Hetero.refl = send⊏recv
      w : treeClock[ e′ ] root≡ treeClock[ e ]
      w = root≡-trans {treeClock[ e′ ]} {t′}{treeClock[ e ]} (join-attach-head {t = treeClock[ e′ ]} eq₂) (root≡-sym {treeClock[ e ]} {t′} (subst (_root≡ t′) (sym eq) x))
      
treeOrder₁ {e = e} {e′ = recv e′ e″ } (there x) | t | node _ _ (_ ∷ ts)| Eq.[ refl ] | Eq.[ eq₂ ] = trans (treeOrder₁ (join-tail-no-new-node {t₁ = treeClock[ e′ ]} {t₂ = treeClock[ e″ ]} eq₂ {t₄ = t}  x )) processOrder₂

treeOrder : ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
            e TC-childOf e′ → e ⊏ e′
treeOrder (immed x) = treeOrder₁ x
treeOrder (recur {e′ = e′} x y) = trans {e′ = e′} (treeOrder x) (treeOrder y)
