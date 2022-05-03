open import Data.List using (List)

module TreeClock.MapTree (K V : Set) where
    
record MapTree : Set where
   inductive
   constructor node
   field
     key : K
     value : V
     children : List MapTree 


  
