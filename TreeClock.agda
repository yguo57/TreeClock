{-# OPTIONS --rewriting #-}
  
open import Event
open import HappensBefore
open import Postulates

open import Data.Bool using (Bool;true;false;not;T;if_then_else_)
open import Data.Empty using (⊥-elim;⊥)
open import Data.Maybe using (Maybe;just;nothing;_<∣>_;_>>=_;fromMaybe)
open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_<?_;_≤_)
open import Data.Fin as Fin using (Fin;fromℕ)
open import Data.Product using (_×_;_,_)
open import Data.List using (List;[];_∷_;foldl;[_])
open import Data.Unit using (⊤)
open import Data.Vec as V hiding (init;[_];[];_∷_)
open import Data.Vec.Relation.Unary.All as All hiding (lookup)
open import Data.Vec.Relation.Unary.AllPairs.Core as AllPairs
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec.Relation.Unary.Unique.Setoid.Properties using (lookup-injective)
open import Function using (case_of_;_∘_)
open import Relation.Nullary using (yes;no;¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary renaming (Decidable to Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl;_≢_;inspect;subst;setoid;≢-sym;sym)

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
    cata alg (node k v cld) = alg k v (cataList alg cld)

 -- TODO stretch : add tree size check
 -- TODO : support attach time of nodes
 
ClockTree = MapTree ProcessId ℕ

lookupNode : ProcessId → ClockTree → Maybe ℕ
lookupNode q (node p n cld) = case q Fin.≟ p of λ where
    (yes _) → just n
    (no  _) → go cld
  where
    go : List ClockTree → Maybe ℕ
    go []       = nothing
    go (t ∷ ts) = (lookupNode q t) <∣> (go ts)

updateNode : ProcessId → ℕ → ClockTree → Maybe ClockTree 
updateNode  q m (node p n cld) = case q Fin.≟ p of λ where
     (yes _) → just (node p m cld)
     (no  _) → helper (go cld)
  where
    go :  List ClockTree → List ClockTree
    go []       = []
    go (t ∷ ts) with updateNode q m t
    ... | just t′ =  t′ ∷ ts
    ... | nothing = go ts
    helper : List ClockTree → Maybe ClockTree
    helper []       = nothing
    helper (t ∷ ts) = just (node p m  (t ∷ ts))

 -- remove all nodes with the given processId
 -- all children are removed along with parent
removeNode : ProcessId →  ClockTree → Maybe ClockTree 
removeNode q (node p n cld) = case q Fin.≟ p of λ where
     (yes _) → nothing
     (no  _) → just (node p n (go cld))
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
initTree p = node p 0 []

inc : ClockTree → ClockTree
inc (node p n cld) =  node p (suc n) cld

pushChild : ClockTree → ClockTree → ClockTree
pushChild t (node p n cld) = node p n (t ∷ cld)

 -- discover if updated nodes in the first tree compared to the second tree
 
getUpdatedNodesJoin : ClockTree →  ClockTree → Maybe ClockTree
getUpdatedNodesJoin (node p n cld) t′ = case lookupNode p t′ of λ where
    nothing  → just (node p n (go cld))
    (just m) → case m <? n of λ where (yes _ ) → just (node p n (go cld)); (no _) → nothing
  where
    go : List ClockTree  → List ClockTree
    go []       = []
    go (t ∷ ts) = appendMaybe (getUpdatedNodesJoin t t′ )(go ts)

 -- detach nodes present in the first tree from the second
 
detachNodes : ClockTree →  ClockTree → Maybe ClockTree
detachNodes (node p _ cld) t = removeNode p t >>= (λ t′ → go cld t′)
  where
    go : List ClockTree → ClockTree → Maybe ClockTree
    go []       t′     = just t′
    go (t ∷ ts) t′     = detachNodes t t′ >>= go ts 
  
 -- joing the first tree to the second
 
join : ClockTree → ClockTree → ClockTree
join t₁ t₂ with getUpdatedNodesJoin t₁ t₂
... | nothing  = t₂
... | just t₁′ with detachNodes t₁′ t₂
...             | nothing  = t₁′
...             | just t₂′ = pushChild t₁′ t₂′

treeClock[_] : Event pid eid → ClockTree
treeClock[_] {pid} init = initTree pid
treeClock[_] {pid} (send x e) = inc treeClock[ e ]
treeClock[_] {pid} (recv e′ e) = join treeClock[ e′ ] treeClock[ e ]


module _ where

  postulate
    m₁ m₂ m₃ m₄ m₅ : Message
    p₁ p₂ p₃ p₄ : ProcessId
    
  pVec = p₁ V.∷ p₂ V.∷ p₃ V.∷ p₄ V.∷ V.[]

  postulate
    unique : Unique pVec
    unique-Fin-≢ : ∀{p q : ProcessId} (neq₁ : p ≢ q) (neq₂ : p ≢ q) → neq₁ ≡ neq₂

  unique⇒≢ : ∀ i j → {T (not ⌊ i Fin.≟ j ⌋)} → lookup pVec i ≢ lookup pVec j
  unique⇒≢ i j x with no ≢ ← i Fin.≟ j = ≢ (lookup-injective (setoid ProcessId) unique i j x)
  
  ≢⇒≟-no : ∀{p q : ProcessId} (neq : p ≢ q) → (p Fin.≟ q) ≡ no neq
  ≢⇒≟-no {p} {q} neq with p Fin.≟ q
  ... | no  neq₂ = Eq.cong no (unique-Fin-≢ neq₂ neq)
  ... | yes eq   = ⊥-elim (neq eq)

  distinctInVec : ∀{n} → ProcessId → ProcessId → Vec ProcessId n →  Bool
  distinctInVec x y V.[] = false
  distinctInVec x y (h V.∷ t) with x Fin.≟ h | y Fin.≟ h
  ... | yes _ | yes _ = false
  ... | no _  | yes _ = true
  ... | yes _ | no _  = true
  ... | no _  | no _  = false  
  
  postulate
    all₀ : ∀{p q : ProcessId} → p ≡ q
    all₁ : ∀{p q : ProcessId} → p ≢ q
    all₂ : ∀{p q : ProcessId} → (p Fin.≟ q) ≡ (if (distinctInVec p q pVec) then yes all₀ else no all₁)
    
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite
  
  {-# REWRITE all₂  #-}
 
  ev₁₁ : Event p₁ 1
  ev₁₁ = send m₁ init
  
  tree₁₁ : ClockTree
  tree₁₁ = node p₁ 1 []
  
  _ : treeClock[ ev₁₁ ] ≡ tree₁₁
  _ = refl

  ev₂₁ : Event p₂ 2
  ev₂₁ = send m₂ (recv ev₁₁ init)

  tree₂₁ : ClockTree
  tree₂₁ = inc (node p₂ 0 [ tree₁₁ ])

  test₁ :  treeClock[ ev₂₁ ] ≡ tree₂₁
  test₁  = refl 

  ev₂₂ : Event p₂ 3
  ev₂₂ = send m₃ ev₂₁

  ev₃₁ : Event p₃ 2
  ev₃₁ = send m₄ (recv ev₂₁ init)

  ev₃₂ : Event p₃ 3
  ev₃₂ = send m₅ ev₃₁

  ev₄₁ : Event p₄ 1
  ev₄₁ = recv ev₂₂ init

  ev₄₂ : Event p₄ 2
  ev₄₂ = recv ev₃₂ ev₄₁

  test₂ : treeClock[ ev₄₁ ] ≡ node p₄ 0 (node p₂ 2 (node p₁ 1 [] ∷ []) ∷ [])
  test₂ = refl
  
  test₃ : treeClock[ ev₄₂ ] ≡ ?
  test₃  = ?
