------------------------------------------------------------------------
-- alternative version of helper functions using catamorphisms
------------------------------------------------------------------------

open import Data.Nat using (ℕ;zero;suc;_≟_;_<_;_<?_;_≤_)

module TreeClockCata (n : ℕ) (Message : Set) where

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
   
mutual
    cataList : ∀{ℓ} {T : Set ℓ} {K V}  → (K → V → List T → T) → List (MapTree K V) → List T
    cataList _   [] = []
    cataList alg (x ∷ xs) = cata alg x ∷ cataList alg xs

    cata : ∀{ℓ} {T : Set ℓ} {K V} → (K → V → List T → T) → MapTree K V → T
    cata alg (node k v ts) = alg k v (cataList alg ts)

 -- TODO stretch : add tree size check
 
ClockTree = MapTree ProcessId (ℕ × ℕ)

 -- catamorphism is not useful when early termination is needed, which is the case for lookupNode and removeNode

updateNode : ProcessId → (ℕ × ℕ) → ClockTree → ClockTree 
updateNode q m t = cata alg t
  where
    alg : ProcessId → (ℕ × ℕ) → List ClockTree → ClockTree
    alg p n [] = node p n [] 
    alg p n ts = case q Fin.≟ p of λ where (yes _) → node p m ts; (no  _) →  node p n ts
