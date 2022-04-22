open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_≤?_;_≤_;_<?_)

module TreeClock.TreeClock (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import Event.HappensBefore n Message

open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe;just;nothing;_<∣>_;_>>=_;fromMaybe;boolToMaybe)
open import Data.Fin as Fin using (Fin;fromℕ)
open import Data.Fin.Properties using ( <-isStrictTotalOrder)
open import Data.Product using (_×_;_,_;map₁;proj₁)
open import Data.List using (List;[];_∷_;foldl;[_];_++_)
open import Data.Unit using (⊤)
open import Data.Vec as V hiding (init;[_];[];_∷_;lookup;remove;_++_)
open import Data.Tree.AVL.Map (record { Carrier = _; _≈_ = _ ; _<_ = _ ; isStrictTotalOrder = <-isStrictTotalOrder {n}}) as Map using (Map;lookup)
open import Function using (case_of_)
open import Relation.Nullary using (yes;no;¬_;does)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary renaming (Decidable to Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;inspect;subst)


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

 -- TODO stretch : add tree size check
 -- TODO use if_then_else
 
Value = ℕ × ℕ  -- clock plus attachement time
ClockTree = MapTree ProcessId Value

record TreeClock : Set where
  constructor
    TC
  field
    T : ClockTree
    M : Map ClockTree

getClock : ProcessId → TreeClock → Maybe ℕ
getClock p (TC _ m) = lookup p m >>= λ where (node _ (c , _) _) → just c

 -- update the first nodes with ProcessId q, the old value is returned if there is one
 
updateNode : ProcessId → Value → ClockTree → ClockTree × Maybe Value
updateNode  q v (node p u ts) = if does(q Fin.≟ p)
                                then (node p v ts , just u)
                                else map₁ (node p u) (go ts)
  where
    go :  List ClockTree → List ClockTree × Maybe Value
    go []       = [] , nothing
    go (t ∷ ts) = case updateNode q u t of λ where (t , nothing)   → map₁ (t ∷_) (go ts) 
                                                   (t′ , just val) → (t′ ∷ ts , just val)

 -- remove the first node with the given processId,  the old value is returned if there is one
 -- children are removed along with parent
 
removeNode : ProcessId →  ClockTree → Maybe ClockTree × Maybe Value
removeNode q (node p u ts) = if does(q Fin.≟ p)
                             then nothing , just u
                             else map₁ (λ ts′ → just (node p u ts′)) (go ts)
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
   
 -- lookup the first node with ProcessId q

initClock : ProcessId → TreeClock
initClock p = let t = initTree p in TC t (Map.singleton p t)

 -- discover a list of updated nodes in the first tree compared to the second tree
 -- the first treturn value in the list is the parent of the updated node
 
getUpdatedNodesJoin : TreeClock → TreeClock → List (Maybe ProcessId × ProcessId × Value)
getUpdatedNodesJoin (TC (node p (c , a) ts) _) tc′  =
   -- bug? can't use decToMaybe (c <? c′) 
  case (do c′ ← getClock p tc′; boolToMaybe (does (c ≤? c′))) of λ where
    nothing  → (nothing , p , (c , a)) ∷ (go p c ts)
    (just _) → []
  where
    go : ProcessId → ℕ → List ClockTree  →  List (Maybe ProcessId × ProcessId × Value)
    go _ _ []       = []
    go p c ((node p′ (c′ , a) ts′) ∷ ts) =
      case (do c″ ← getClock p′ tc′; boolToMaybe (does (c″ ≤? c′))) of λ where
         nothing  → (just p , p′ , (c′ , a)) ∷ (go p′ c′ ts′) ++
                    (if does(a ≤? c) then [] else go p c ts)
         (just _) → []


    
--  -- detach nodes present in the first tree from the second
 
-- detachNodes : ClockTree →  ClockTree → Maybe ClockTree
-- detachNodes (node p _ ts) t = proj₁ (removeNode p t) >>= (λ t′ →  go ts t′)
--   where
--     go : List ClockTree → ClockTree → Maybe ClockTree
--     go []       t′     = just t′
--     go (t ∷ ts) t′     = detachNodes t t′ >>= go ts 
  
--  -- joing the first tree to the second
 
-- join : ClockTree → ClockTree → ClockTree
-- join t₁ t₂ with getUpdatedNodesJoin t₁ t₂
-- ... | nothing  = inc t₂
-- ... | just t₁′ with detachNodes t₁′ t₂
-- ...             | nothing  = t₁′
-- ...             | just t₂′ = pushChild t₁′ (inc t₂′)

-- treeClock[_] : Event pid eid → ClockTree
-- treeClock[_] {pid} init = initTree pid
-- treeClock[_] {pid} (send x e) = inc treeClock[ e ]
-- treeClock[_] {pid} (recv e′ e) = join treeClock[ e′ ] treeClock[ e ]


