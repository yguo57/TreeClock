open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_)

module TreeClock.TreeClock (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import Event.HappensBefore n Message

open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe;just;nothing;_<∣>_;_>>=_)
open import Data.Fin as Fin using (Fin;fromℕ)
open import Data.Product using (_×_;_,_;map₁;proj₁)
open import Data.List using (List;[];_∷_;foldl;[_])
open import Data.Unit using (⊤)
open import Data.Vec as V hiding (init;[_];[];_∷_)
open import Function using (case_of_)
open import Relation.Nullary using (yes;no;¬_;does)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary renaming (Decidable to Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

 -- TODO stretch : add tree size check

Value = ℕ × ℕ  -- clock plus attachement time

open import TreeClock.MapTree ProcessId Value as ClockTree

ClockTree = MapTree 

-- util for maybe
appendMaybe : ∀{A : Set} → Maybe A → List A → List A
appendMaybe nothing  xs = xs
appendMaybe (just x) xs = x ∷ xs

 -- lookup the first node with ProcessId q
 
lookupNode : ProcessId → ClockTree → Maybe Value
lookupNode q (node p n ts) = if does (q Fin.≟ p) 
                             then just n
                             else go ts
  where
    go : List ClockTree → Maybe Value
    go []       = nothing
    go (t ∷ ts) = (lookupNode q t) <∣> (go ts)

 -- update the first nodes with ProcessId q, the old value is returned if there is one
 
updateNode : ProcessId → Value → ClockTree → ClockTree × Maybe Value
updateNode  q m (node p n ts) = if does(q Fin.≟ p)
                                then (node p m ts , just n)
                                else map₁ (node p n) (go ts)
  where
    go :  List ClockTree → List ClockTree × Maybe Value
    go []       = [] , nothing
    go (t ∷ ts) = case updateNode q m t of λ where (t , nothing)   → map₁ (t ∷_) (go ts) 
                                                   (t′ , just val) → (t′ ∷ ts , just val)

 -- remove the first node with the given processId,  the old value is returned if there is one
 -- children are removed along with parent
 
removeNode : ProcessId →  ClockTree → Maybe ClockTree × Maybe Value
removeNode q (node p n ts) = if does(q Fin.≟ p)
                             then nothing , just n
                             else map₁ (λ ts′ → just (node p n ts′)) (go ts)
  where
    go : List ClockTree → List ClockTree × Maybe Value
    go []       = [] , nothing
    go (t ∷ ts) = case removeNode q t of λ where (nothing , m)        → (ts , m)
                                                 (just t  , nothing)  → map₁ (t ∷_) (go ts)
                                                 (just t  , just val) → (t ∷ ts , just val)

initTree : ProcessId → ClockTree
initTree p = node p (0 , 0) []

inc : ClockTree → ClockTree
inc (node p (c , a) ts) =  node p (suc c , a) ts

pushChild : ClockTree → ClockTree → ClockTree
pushChild (node q (c , _) ts) (node p n@(c′ , _) ts′) = node p n (newChild ∷ ts′)
  where
   newChild = node q (c , c′) ts

 -- discover any updated nodes in the first tree compared to the second tree

getUpdatedNodesJoin : ClockTree →  ClockTree → Maybe ClockTree
getUpdatedNodesJoin (node p (c , a) ts) t′ =
  case (lookupNode p t′) of λ where
    nothing  → continue
    (just (c′ , _ )) → if does (c <? c′) then nothing else continue
  where
    -- TODO : support early termination using attach time of nodes (only useful with thrMap)
    go : List ClockTree → List ClockTree
    go []       = []
    go (t ∷ ts) = appendMaybe (getUpdatedNodesJoin t t′ )(go ts)
    continue : Maybe ClockTree
    continue = just (node p (c , a)  (go ts))

 -- detach nodes present in the first tree from the second
                        
detachNodes : ClockTree →  ClockTree → Maybe ClockTree
detachNodes (node p _ ts) t = proj₁ (removeNode p t) >>= (λ t′ →  go ts t′)
  where
    go : List ClockTree → ClockTree → Maybe ClockTree
    go []       t′     = just t′
    go (t ∷ ts) t′     = detachNodes t t′ >>= go ts 
  
 -- joing the first tree to the second
 
join : ClockTree → ClockTree → ClockTree
join t₁ t₂ with getUpdatedNodesJoin t₁ t₂
... | nothing  = inc t₂
... | just t₁′ with detachNodes t₁′ t₂
      -- need to eliminate this case by restricting recvs
...             | nothing  = inc t₁′ 
...             | just t₂′ = pushChild t₁′ (inc t₂′)


 -- in the context of tree clocks, send is release and recv is acquire
 
treeClock[_] : Event pid eid → ClockTree
treeClock[_] {pid} init = initTree pid
treeClock[_] {pid} (send x e) = inc treeClock[ e ]
treeClock[_] {pid} (recv e′ e) =  join treeClock[ e′ ] treeClock[ e ]


