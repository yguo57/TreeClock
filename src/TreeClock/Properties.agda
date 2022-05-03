open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_;_<ᵇ_)

module TreeClock.Properties (n : ℕ) (Message : Set) where

open import TreeClock.TreeClock n Message
open import Event.Event n Message
open import TreeClock.MapTree ProcessId Value as ClockTree 
open import Event.HappensBefore n Message
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (_≟_;suc)
open import Data.List using (List;[];_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using(Any;here;there)
open import Data.Maybe.Base using (nothing;just;boolToMaybe)
open import Data.Product using (_×_ ; _,_;Σ-syntax;proj₁;proj₂;uncurry′)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst;cong;sym) renaming (trans to transitive)
open Eq.≡-Reasoning using (step-≡ )
open import Relation.Binary.HeterogeneousEquality as Hetero using (_≅_)
open import Relation.Nullary using (yes; no; does;¬_)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
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
...            | just t₂′ | Eq.[ eq ] rewrite pushChild-fix-rootClk t₁′ (inc t₂′) | rootClk∘inc≡suc∘rootClk t₂′ | detachNodes-fix-rootClk t₁′ t₂ eq = cong suc refl 
...            | nothing  | _ rewrite rootClk∘inc≡suc∘rootClk t₁′ = cong suc {!!}

eid≡rootClk : eid[ e ] ≡ rootClk treeClock[ e ]
eid≡rootClk {_} {zero} {e = init} = refl
eid≡rootClk {_} {(suc _)} {e = send m e}
  with treeClock[ e ] | inspect (treeClock[_]) e
... | (node _ (clk , _)  _) | Eq.[ eq ] = cong suc (transitive (eid≡rootClk {e = e}) (cong rootClk eq))
eid≡rootClk  {_} {suc _} {e = recv e e′} rewrite rootClk∘join≡suc∘rootClk treeClock[ e ] treeClock[ e′ ] = cong suc (eid≡rootClk {e = e′} )

_root≡_ : ClockTree → ClockTree → Set
_root≡_  t t′ = rootPid t ≡ rootPid t′ × rootClk t ≡ rootClk t′

open ClockTree.ChildOf _root≡_

postulate
  join-attach-head : ∀ {k v ts t t′ t″} →  join t t′ ≡ node k v (t″ ∷ ts) → t root≡ t″
  join-tail-no-new-node : ∀ {k v ts t₁ t₂ t₃} →  join t₁ t₂ ≡ node k v (t₃ ∷ ts) → ∀{t₄} → t₄ t∈ ts → t₄ t∈ (rootChild t₂)
  pid≡rootPid : pid[ e ] ≡ rootPid treeClock[ e ]
  
root≡-trans : ∀ {t t′ t″} → t root≡ t′ → t′ root≡ t″ → t root≡ t″
root≡-trans (a , b) (c , d) =  transitive a c , transitive b d

root≡-sym : ∀ {t t′} → t root≡ t′ → t′ root≡ t
root≡-sym (a , b) =  sym a , sym b

root≡⇒Pid≡×Clk≡ : treeClock[ e ] root≡ treeClock[ e′ ] → pid[ e ] ≡ pid[ e′ ] × eid[ e ] ≡ eid[ e′ ]
root≡⇒Pid≡×Clk≡ {e = e} {e′ = e′} (a , b) = transitive (transitive (pid≡rootPid {e = e}) a) (sym (pid≡rootPid {e = e′}) ) , transitive (transitive (eid≡rootClk {e = e})  b) (sym (eid≡rootClk {e = e′}))


_Ev-childOf′_ : Event pid eid → Event pid′ eid′ → Set 
e Ev-childOf′ e′ =  treeClock[ e ] childOf treeClock[ e′ ]

data _Ev-childOf_ : Event pid eid → Event pid′ eid′ → Set where
  immed : e Ev-childOf′ e′ → e Ev-childOf e′
  recur : e Ev-childOf′ e′ → e′ Ev-childOf′ e″ → e Ev-childOf e″ 

inc-irrelev-child :  ∀ t →  rootChild (inc t) ≡ rootChild t
inc-irrelev-child (node _ _ ts) = refl

inc-irrelev-childOf₁ : ∀ t t′ → t childOf t′ → t childOf (inc t′)
inc-irrelev-childOf₁ t t′ x = subst (t t∈_) (sym (inc-irrelev-child t′)) x 

inc-irrelev-childOf₂ :  ∀ t t′ → t childOf (inc t′) → t childOf t′
inc-irrelev-childOf₂ t t′ x = subst (t t∈_ )  (inc-irrelev-child  t′) x 

treeOrder′ : ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
            e Ev-childOf′ e′ → e ⊏ e′
treeOrder′ {e = e} {e′ = e′} x  with treeClock[ e ] | treeClock[ e′ ] | inspect treeClock[_] e | inspect treeClock[_] e′
treeOrder′ {e = e} {e′ = init} ()               | _ | node _ _ [] | _ | _
treeOrder′ {e = e} {e′ = send _ e′} x           | t | _ | Eq.[ refl ] | Eq.[ eq ]  with  y ← treeOrder′ {e = e} (inc-irrelev-childOf₂ t treeClock[ e′ ] (subst (treeClock[ e ] childOf_) (sym eq) x )) = trans y processOrder₁
treeOrder′ {e = e} {e′ = recv e′ e″} (here x)   | _ | node _ _ (t′ ∷ _) | Eq.[ eq ] | Eq.[ eq₂ ] = helper (uncurry′ uniquely-identify (root≡⇒Pid≡×Clk≡ {e = e′} {e′ = e} w))
  where
      helper : e′ ≅ e → e ⊏ recv e′ e″
      helper Hetero.refl = send⊏recv
      y : treeClock[ e′ ] root≡ t′
      y = join-attach-head {t = treeClock[ e′ ]} eq₂
      z : treeClock[ e ] root≡ t′
      z = subst (_root≡ t′) (sym eq) x
      w : treeClock[ e′ ] root≡ treeClock[ e ]
      w = root≡-trans {treeClock[ e′ ]} {t′}{treeClock[ e ]}  y (root≡-sym {treeClock[ e ]} {t′}  z)
      
treeOrder′ {e = e} {e′ = recv e′ e″ } (there x) | t | node _ _ (_ ∷ ts)| Eq.[ refl ] | Eq.[ eq₂ ] = trans (treeOrder′ (join-tail-no-new-node {t₁ = treeClock[ e′ ]} {t₂ = treeClock[ e″ ]} eq₂ {t₄ = t}  x )) processOrder₂

treeOrder : ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
            e Ev-childOf e′ → e ⊏ e′
treeOrder (immed x) = treeOrder′ x
treeOrder (recur {e′ = e′} x y) = trans {e′ = e′} (treeOrder′ x) (treeOrder′ y)
