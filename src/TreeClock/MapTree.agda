open import Data.List using (List;[];_∷_)
open import Data.List.Relation.Unary.Any using(Any;here;there)
open import Relation.Binary.Definitions using (Transitive)

module TreeClock.MapTree (K V : Set) where
    
data MapTree : Set where
   node : K → V → List MapTree → MapTree
    
rootChild : MapTree → List MapTree
rootChild (node _ _ ts) = ts

module ChildOf (_t≡_ : MapTree → MapTree → Set) where

  _t∈_ : MapTree → List MapTree → Set 
  _t∈_  t ts = Any (t  t≡_) ts

  -- alternative definition
  -- data _childOf_ : MapTree → MapTree → Set where
  --     immed : (t : MapTree) → (t′ : MapTree) → t t∈ (rootChild t′) → t childOf t′
  
  _childOf_ : MapTree → MapTree → Set
  t childOf t′  = t t∈ (rootChild t′)


  
