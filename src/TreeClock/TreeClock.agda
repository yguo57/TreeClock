open import Data.Nat using (ℕ;zero;suc;_<?_)

module TreeClock.TreeClock (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import Event.HappensBefore n Message
open import Event.Clock n Message

open import Data.Bool using (if_then_else_; true;false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; fromℕ)
open import Data.Fin as Fin using (Fin; fromℕ)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_; _>>=_; maybe′)
open import Data.Nat.Properties using (<⇒≤)
open import Data.Product using (_×_; _,_; map₁; proj₁; proj₂)
open import Data.List using (List; []; _∷_; foldl; [_])
open import Data.Unit using (⊤)
open import Data.Vec as V hiding (init; [_]; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (does)


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

open import TreeClock.MapTree ProcessId Value

ClockTree = MapTree
open MapTree

rootPid : ClockTree → ProcessId
rootPid t = MapTree.key t

rootClk : ClockTree → ℕ
rootClk t = proj₁ (MapTree.value t)

rootAclk : ClockTree → ℕ
rootAclk t = proj₂ (MapTree.value t)

 -- lookup the first node with ProcessId q
 
lookupNode : ProcessId → ClockTree → Maybe Value
lookupNode q (node p n ts) = if does (q Fin.≟ p) 
                             then just n
                             else go ts
  module lookupNode where
    go : List ClockTree → Maybe Value
    go []       = nothing
    go (t ∷ ts) = (lookupNode q t) <∣> (go ts)

lookupClk : ProcessId → ClockTree → ℕ
lookupClk q t = case lookupNode q t of λ where 
                    (just (c , _)) → c
                    nothing → 0
                
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
 
removeNode : ProcessId →  ClockTree → Maybe ClockTree × Maybe ClockTree
removeNode q t@(node p n ts) = if does(q Fin.≟ p)
                             then nothing , just t
                             else map₁ (λ ts′ → just (node p n ts′)) (go ts)
  module removeNode where
    go : List ClockTree → List ClockTree × Maybe ClockTree
    go []       = [] , nothing
    go (t ∷ ts) = case removeNode q t of λ where (nothing , t′)        → (ts , t′)
                                                 (just t  , nothing)  → map₁ (t ∷_) (go ts)
                                                 (just t  , mt′) → (t ∷ ts , mt′)

initTree : ProcessId → ClockTree
initTree p = node p (0 , 0) []

inc : ClockTree → ClockTree
inc (node p (c , a) ts) =  node p (suc c , a) ts

pushChild : ClockTree → ClockTree → ClockTree
pushChild (node q (c , _) ts) (node p n@(c′ , _) ts′) = node p n (newChild ∷ ts′)
  where
   newChild = node q (c , c′) ts

 -- discover any updated nodes in the first tree compared to the second tree
 -- TODO: add support for attachment time

getUpdatedNodesJoin : ClockTree →  ClockTree → Maybe ClockTree
getUpdatedNodesJoin (node p (c , a) ts) t′ =
  case (lookupNode p t′) of λ where
    nothing  → continue
    (just (c′ , _ )) → if does (c <? c′) then nothing else continue
  module getUpdatedNodesJoin where
    go : List ClockTree → List ClockTree
    go []       = []
    go (t ∷ ts) = maybe′ (_∷ go ts) (go ts) (getUpdatedNodesJoin t t′ )
    continue : Maybe ClockTree
    continue = just (node p (c , a)  (go ts))

 -- detach key present in the second tree from the first tree, if the root of the first tree is detached, return the node the caused it

detachNodes : ClockTree →  ClockTree → Maybe ClockTree
detachNodes t t′ = proj₁ (removeNode (key t′) t) >>= go (children t′)
   module detachNodes where
    go : List ClockTree → ClockTree → Maybe ClockTree
    go []        t     = just t
    go (t′ ∷ ts) t     = detachNodes t t′ >>= go (children t′)
   
 -- shift the root of the given Clocktree to the given pid, leaving other nodes unchanged

shiftRoot : ProcessId → ClockTree → ClockTree
shiftRoot p t = case removeNode p t of λ where
                     (_ , nothing)  → pushChild t (node p (0 , 0) [])
                     (nothing , just n) → n
                     (just t′ , just n) → pushChild t′ n  

 -- joing the first tree to the second
 
join : ClockTree → ClockTree → ClockTree
join t₁ t₂ with getUpdatedNodesJoin t₁ t₂
... | nothing  = inc t₂
... | just t₁′ with detachNodes t₂ t₁′
      -- it'd be nice if we could eliminate this case by restricting recvs from the future
...             | nothing  = inc (shiftRoot (rootPid t₂) t₁′) 
...             | just t₂′ = pushChild t₁′ (inc t₂′)


 -- in the context of tree clocks, send is release and recv is acquire
 
treeClock[_] : Event pid eid → ClockTree
treeClock[_] {pid} init = initTree pid
treeClock[_] {pid} (send x e) = inc treeClock[ e ]
treeClock[_] {pid} (recv e′ e) =  join treeClock[ e′ ] treeClock[ e ]

