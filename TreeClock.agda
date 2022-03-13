open import Event
open import HappensBefore
open import Postulates

open import Data.Bool using (Bool;true;false)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ;suc;_≟_)
open import Data.Fin as Fin using (Fin)
open import Data.Product using (_×_;_,_)
open import Data.List using (List;[];_∷_;foldl)
open import Relation.Nullary using (yes;no)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″
 
 -- strech : add tree size check
 -- TODO : support attach time of nodes
data MapTree (K : Set) (V : Set) : Set where
   node : K → V → List (MapTree K V) → MapTree K V

-- util methods

lookupNode : ∀{K V} → K → MapTree K V → Maybe V
lookupNode = {!!}

insertNode : ∀{K V} → K → MapTree K V → MapTree K V
insertNode = {!!}

removeNode : ∀{K V} → K → MapTree K V →  MapTree K V
removeNode = {!!}

ClockTree = MapTree ProcessId ℕ

isUpdated : ProcessId → ℕ → ClockTree → Bool
isUpdated = {!!}

-- if needs threadMap
-- record TreeClock : Set where
--   constructor tc
--   field 
--     tree   : ClockTree
--     thrMap : ProcessId → ClockTree

initTree : ProcessId → ClockTree
initTree p = node p 0 []

inc : ClockTree → ClockTree
inc (node p n cld) =  node p (suc n) cld

pushChild : ClockTree → ClockTree → ClockTree
pushChild t (node p n cld) = node p n (t ∷ cld)

 -- dicover nodes in the tree list that has been updated compared to the second tree
 
getUpdatedNodesJoin : List ClockTree → ClockTree → List ClockTree
getUpdatedNodesJoin []                     t′ = []
getUpdatedNodesJoin ((node p n cld) ∷ ts)  t′ with isUpdated p n t′
... | true  = (node p n (getUpdatedNodesJoin cld t′)) ∷ getUpdatedNodesJoin ts t′
... | false = getUpdatedNodesJoin ts t′

 -- detach nodes present in the first tree from the second
 
detachNodes : ClockTree →  ClockTree → ClockTree
detachNodes (node p _ cld) t = go cld (removeNode p t)
  where
    go : List ClockTree → ClockTree → ClockTree
    go []        t′     = t′
    go (t′ ∷ ts) t″     = go ts (detachNodes t′ t″)
  
 -- joing the first tree to the second
 
join :  ClockTree → ClockTree → ClockTree
join (node pid n cld) t₂  with isUpdated pid n t₂
... | false = t₂
... | true = 
  let t₁  = node pid n (getUpdatedNodesJoin cld t₂)
      t₂′ = detachNodes t₁ t₂
  in pushChild t₁ t₂′

treeClock[_] :  Event pid eid →  ClockTree
treeClock[_] {pid} init = initTree pid
treeClock[_] {pid} (send x e) = inc treeClock[ e ]
treeClock[_] {pid} (recv e′ e) = join treeClock[ e′ ] treeClock[ e ]
