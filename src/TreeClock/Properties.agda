open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_;_<ᵇ_)

module TreeClock.Properties (n : ℕ) (Message : Set) where

open import TreeClock.TreeClock n Message
open import Event.Execution n Message
open import Event.HappensBefore n Message
open import Event.WellFormed n Message
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (_≟_;suc)
open import Data.List using (List;[];_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using(Any;here;there)
open import Data.Maybe.Base using (nothing;just;boolToMaybe)
open import Data.Product using (_×_ ; _,_;Σ-syntax;proj₁;proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst;cong) renaming (trans to transitive)
open import Relation.Binary.HeterogeneousEquality using (_≅_)
open import Relation.Nullary using (yes; no; does)

private
  variable
    pid pid′ pid″ : ProcessId
    m  : Message
    e  : Event pid 
    e′ : Event pid′ 
    e″ : Event pid″
    wf : Wellformed e
    wf′ : Wellformed e′
    wf″ : Wellformed e″
    

rootPid : ClockTree → ProcessId
rootPid (node pid _  _) = pid

rootClk : ClockTree → ℕ
rootClk (node _ (clk , _)  _) = clk

rootAclk : ClockTree → ℕ
rootAclk (node _ ( _ , aclk )  _) = aclk

-- postulate
--   rootClk∘inc≡suc∘rootClk : ∀ t → rootClk (inc t) ≡ suc (rootClk t)
--   getUpdatedNodesJoin-fix-rootClk : ∀ t₁ t₂ {t₁′} → getUpdatedNodesJoin t₁ t₂ ≡ just t₁′ → rootClk t₁′ ≡ rootClk t₁
--   detachNodes-fix-rootClk : ∀ t₁ t₂ {t₂′} → detachNodes t₁ t₂ ≡ just t₂′ → rootClk t₂′ ≡ rootClk t₂
--   pushChild-fix-rootClk : ∀ t₁ t₂ → rootClk (pushChild t₁ t₂)  ≡ rootClk t₂
                                                                                      
-- rootClk∘join≡suc∘rootClk  : ∀ t t′ →  rootClk (join t t′) ≡ suc (rootClk t′)
-- rootClk∘join≡suc∘rootClk t₁@(node pid (clk , _) _) t₂@(node pid′ (clk′ , _) _)
--   with getUpdatedNodesJoin t₁ t₂  | inspect (getUpdatedNodesJoin t₁) t₂
-- ... | nothing  | _  rewrite rootClk∘inc≡suc∘rootClk t₁  = cong suc refl
-- ... | just t₁′ | Eq.[ eq ] with detachNodes t₁′ t₂ | inspect (detachNodes t₁′) t₂
-- ...            | just t₂′ | Eq.[ eq ] rewrite pushChild-fix-rootClk t₁′ (inc t₂′) | rootClk∘inc≡suc∘rootClk t₂′ | detachNodes-fix-rootClk t₁′ t₂ eq = cong suc refl 
-- ...            | nothing  | _ rewrite rootClk∘inc≡suc∘rootClk t₁′ = cong suc {!!}

-- eid≡clk : ∀ (e : Event pid eid) → eid ≡ rootClk treeClock[ e ]
-- eid≡clk {_} {zero} init = refl
-- eid≡clk {_} {(suc _)} (send m e)
--   with treeClock[ e ] | inspect (treeClock[_]) e
-- ... | (node _ (clk , _)  _) | Eq.[ eq ] = cong suc (transitive (eid≡clk e) (cong rootClk eq))
-- eid≡clk  {_} {suc _} (recv e e′) rewrite rootClk∘join≡suc∘rootClk treeClock[ e ] treeClock[ e′ ] = cong suc (eid≡clk e′)

_TC-root≡_ : ClockTree → ClockTree → Set 
_TC-root≡_  t t′ = rootPid t ≡ rootPid t′ × rootClk t ≡ rootClk t′

data _childOf_ {K : Set} {V : Set} {_tree≡_ : MapTree K V → MapTree K V → Set}  : MapTree K V → MapTree K V → Set where
  immed : ∀ {k : K} {v : V} {ts : List (MapTree K V)} → (t : MapTree K V) → Any (t tree≡_)  ts → t childOf (node k v ts)
  trans : ∀{t₁ t₂ t₃} → _childOf_ {_tree≡_ = _tree≡_ } t₁ t₂ → _childOf_ { _tree≡_  = _tree≡_ } t₂ t₃ → t₁ childOf t₃

_TC-childOf_ = _childOf_{_tree≡_ = _TC-root≡_}

inc-irrelev-child :  ∀{k v k′ v′ ts ts′} →  inc (node k′ v′ ts′) ≡ (node k v ts) → ts ≡ ts′
inc-irrelev-child {ts = ts} {ts′ = .ts} refl = refl

inc-irrelev-childOf₁ : ∀ {t t′} → (t TC-childOf t′) → (t TC-childOf (inc t′))
inc-irrelev-childOf₁ (immed _ x) = immed _ x
inc-irrelev-childOf₁ (trans x y) = trans x (inc-irrelev-childOf₁ y)

inc-irrelev-childOf₂ : ∀ {t t′} → (t TC-childOf (inc t′)) → (t TC-childOf t′)
inc-irrelev-childOf₂ {t′ = t′} x            with inc t′  | inspect inc t′ 
inc-irrelev-childOf₂ {t′ = node _ _ ts′} (immed _ x)    | _  | Eq.[ eq ] rewrite inc-irrelev-child eq = immed _ x
inc-irrelev-childOf₂ {t′ = t′} (trans x y)              | _  | Eq.[ refl ] = trans x (inc-irrelev-childOf₂ y)

 -- plan:
 -- 1.
 -- lemma1 : treeClock[ e ] TC-childOf treeClock[ e′ ] → ∃[ e₁ ]  treeClock[ e₁ ] TC-tree≡ treeClock[ e ] ×  e₁ ⊏ e′
 -- 2. prove rootClk is unique on a given process in a given execution
-- rootClk-unique :  same-origin e e′ → treeClock[ e , wf ] TC-root≡ treeClock[ e′ , wf′ ] → e ≡ e

treeOrder : same-origin e e′ → treeClock[ e , wf ] TC-childOf treeClock[ e′ , wf′ ] → e ⊏ e′
treeOrder {e = e} {e′ = e′} {wf = wf} {wf′ = wf′} s x  with treeClock[ e , wf ] | treeClock[ e′ , wf′ ] | inspect treeClock[ e ,_] wf | inspect treeClock[ e′ ,_] wf′ 
treeOrder {e = e} {e′ = init} _ (immed _ _)          | _ | (node _ _ (_ ∷ _))  | _           | ()
treeOrder {e = e} {e′ = send m e′} {wf′ = wf-send wf′} s x                    | t | _                   | Eq.[ refl ] | Eq.[ refl ]  with y ← treeOrder {e = e} {!!}  (inc-irrelev-childOf₂ x) =  trans y processOrder₁
treeOrder {e = e} {e′ = recv e′ e′₁} s (immed _ x) | node k v _ | node _ _ (node k′ v′ _ ∷ _) | _ | _ = {!!}
treeOrder {e = e} {e′ = e′} s (trans x x₁)           | _ | t | _ | _ = {!!}


