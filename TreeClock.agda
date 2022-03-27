open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_<?_;_≤_)

module TreeClock (n : ℕ) (Message : Set) where

open import Event n Message
open import HappensBefore n Message

open import Data.Maybe using (Maybe;just;nothing;_<∣>_;_>>=_;fromMaybe)
open import Data.Fin as Fin using (Fin;fromℕ)
open import Data.Product using (_×_;_,_)
open import Data.List using (List;[];_∷_;foldl;[_])
open import Data.Unit using (⊤)
open import Data.Vec as V hiding (init;[_];[];_∷_)
open import Function using (case_of_)
open import Relation.Nullary using (yes;no;¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary renaming (Decidable to Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)

-- util for maybe
appendMaybe : ∀{A : Set} → Maybe A → List A → List A
appendMaybe nothing  xs = xs
appendMaybe (just x) xs = x ∷ xs

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″


data MapTree (K : Set) (V : Set) : Set where
   node : K → V → List (MapTree K V) → MapTree K V
   
 -- TODO use catamorphism
mutual
    cataList : ∀{ℓ} {T : Set ℓ} {K V}  → (K → V → List T → T) → List (MapTree K V) → List T
    cataList _   [] = []
    cataList alg (x ∷ xs) = cata alg x ∷ cataList alg xs

    cata : ∀{ℓ} {T : Set ℓ} {K V} → (K → V → List T → T) → MapTree K V → T
    cata alg (node k v ts) = alg k v (cataList alg ts)

 -- TODO stretch : add tree size check
 
ClockTree = MapTree ProcessId (ℕ × ℕ)

lookupNode : ProcessId → ClockTree → Maybe (ℕ × ℕ)
lookupNode q (node p n ts) = case q Fin.≟ p of λ where
    (yes _) → just n
    (no  _) → go ts
  where
    go : List ClockTree → Maybe (ℕ × ℕ)
    go []       = nothing
    go (t ∷ ts) = (lookupNode q t) <∣> (go ts)

updateNode : ProcessId → (ℕ × ℕ) → ClockTree → Maybe ClockTree 
updateNode  q m (node p n ts) = case q Fin.≟ p of λ where
     (yes _) → just (node p n ts)
     (no  _) → helper (go ts)
  where
    go :  List ClockTree → List ClockTree
    go []       = []
    go (t ∷ ts) with updateNode q m t
    ... | just t′ =  t′ ∷ ts
    ... | nothing = go ts
    helper : List ClockTree → Maybe ClockTree
    helper []       = nothing
    helper (t ∷ ts) = just (node p m (t ∷ ts))

 -- remove all nodes with the given processId
 -- all children are removed along with parent
removeNode : ProcessId →  ClockTree → Maybe ClockTree 
removeNode q (node p n ts) = case q Fin.≟ p of λ where
     (yes _) → nothing
     (no  _) → just (node p n (go ts))
  where
    go : List ClockTree → List ClockTree
    go []       = []
    go (t ∷ ts) = appendMaybe (removeNode q t) (go ts)

-- if needs threadMap
-- record TreeClock : Set where
--   constructor tc
--   field 
--     tree   : ClockTree
--     thrMap : ProcessId → ClockTree

initTree : ProcessId → ClockTree
initTree p = node p (0 , 0) []

inc : ClockTree → ClockTree
inc (node p (c , a) ts) =  node p (suc c , a) ts

pushChild : ClockTree → ClockTree → ClockTree
pushChild (node q (c , _) ts) (node p n@(c′ , _) ts′) = node p n (newChild ∷ ts′)
  where
   newChild = node q (c , c′) ts

 -- TODO : support early termination using attach time of nodes (only useful with thrMap)
 -- discover any updated nodes in the first tree compared to the second tree

getUpdatedNodesJoin : ClockTree →  ClockTree → Maybe ClockTree
getUpdatedNodesJoin (node p (c , a) ts) t′ = case lookupNode p t′ of λ where
    nothing  → just (node p (c , a)  (go ts))
    (just (c′ , a′)) →
      case c′ <? c of λ where
        (yes _ ) → just (node p (c , a) (go ts))
        (no _) → nothing
  where
    go : List ClockTree  → List ClockTree
    go []       = []
    go (t ∷ ts) = appendMaybe (getUpdatedNodesJoin t t′ )(go ts)

 -- detach nodes present in the first tree from the second
 
detachNodes : ClockTree →  ClockTree → Maybe ClockTree
detachNodes (node p _ ts) t = removeNode p t >>= (λ t′ → go ts t′)
  where
    go : List ClockTree → ClockTree → Maybe ClockTree
    go []       t′     = just t′
    go (t ∷ ts) t′     = detachNodes t t′ >>= go ts 
  
 -- joing the first tree to the second
 
join : ClockTree → ClockTree → ClockTree
join t₁ t₂ with getUpdatedNodesJoin t₁ t₂
... | nothing  = inc t₂
... | just t₁′ with detachNodes t₁′ t₂
...             | nothing  = t₁′
...             | just t₂′ = pushChild t₁′ (inc t₂′)

treeClock[_] : Event pid eid → ClockTree
treeClock[_] {pid} init = initTree pid
treeClock[_] {pid} (send x e) = inc treeClock[ e ]
treeClock[_] {pid} (recv e′ e) = join treeClock[ e′ ] treeClock[ e ]
