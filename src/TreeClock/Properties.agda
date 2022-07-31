open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; _≤?_; _≤_; _<?_; _<ᵇ_)

module TreeClock.Properties (n : ℕ) (Message : Set) where

open import Event.Event n Message
open import TreeClock.MapTree
open MapTree
open import TreeClock.TreeClock n Message

open import Data.Product using (proj₁)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin as Fin using (_≟_)
open import Data.List using ([]; _∷_)
open import Relation.Nullary using (yes; no; ¬_;does)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary renaming (Decidable to Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; inspect; subst; _≢_; cong;trans;sym)
    
inc-preserves-pid : ∀ {t} → rootPid t ≡ rootPid (inc t)
inc-preserves-pid = refl

removeNodes-preserves-pid : ∀ pid t t₁ → proj₁ (removeNode pid t) ≡ just t₁ → rootPid t ≡ rootPid t₁
removeNodes-preserves-pid pid t _ _
  with pid Fin.≟ key t 
     | proj₁(removeNode pid t) | inspect proj₁ (removeNode pid t)
removeNodes-preserves-pid pid t .y refl | yes _  | just y | Eq.[ () ] 
removeNodes-preserves-pid pid t .y refl | no _   | just y | Eq.[ z ] = cong key (just-injective z)

detachNodes-preserves-pid : ∀ t t′ t₁ → detachNodes t t′ ≡ just t₁ → rootPid t ≡ rootPid t₁
detachNodes-preserves-pid  t t′ t₁ x
  with proj₁ (removeNode (key t′) t)  | inspect proj₁ (removeNode (key t′) t) 
detachNodes-preserves-pid  t t′ _ () | nothing | Eq.[ y ]
detachNodes-preserves-pid  t t′@(node _ _ []) _ x | just t₂ | Eq.[ y ]
  with w ← removeNodes-preserves-pid (key t′) t t₂ y
  = trans w (cong key (just-injective  x))
detachNodes-preserves-pid  t t′@(node _ _ (t₃ ∷ _)) _ x | just t₂ | Eq.[ y ]
  with w ← removeNodes-preserves-pid (key t′) t t₂ y
  = {!!}

-- lesson: properties like pid≡rootPid that span multiple recursive functions should be proved on these functions separately.

-- detachNodesGo-preserves-pid : ∀ {k v ts t ts″ t′ t″} → detachNodes.go k v ts t ts″ t′ ≡ just t″ → rootPid t′ ≡ rootPid t″
-- detachNodesGo-preserves-pid {k}{v} {ts} {t} {[]} {t′} {t″} x with detachNodes.go k v ts t [] t′ | inspect (detachNodes.go k v ts t []) t′+
-- ... | just (node p _ _ ) | Eq.[ y ] = cong rootPid (just-injective (Eq.trans y x))
-- detachNodesGo-preserves-pid {k}{v} {ts} {t} {th ∷ tt} {t′} {t″} x with detachNodes.go k v ts t (th ∷ tt) t′ | inspect (detachNodes.go k v ts t (th ∷ tt)) t′ | removeNode.go (MapTree.key th) (MapTree.key t′) (MapTree.value t′) (MapTree.children t′) (MapTree.children t′) | inspect (removeNode.go (MapTree.key th) (MapTree.key t′) (MapTree.value t′) (MapTree.children t′)) (MapTree.children t′) 
-- ... | v | Eq.[ y ] | w | Eq.[ z ] rewrite z with MapTree.key th Fin.≟ MapTree.key t′ | (detachNodes.go (MapTree.key th) (MapTree.value th)(MapTree.children th) t′ (MapTree.children th) (node (MapTree.key t′) (MapTree.value t′) (proj₁ w)))
-- detachNodesGo-preserves-pid {k}{v} {ts} {t} {th ∷ tt} {t′} {t″} x | s | Eq.[ y ] | w | Eq.[ z ] | no _ | just u with detachNodes.go (MapTree.key th) (MapTree.value th) (MapTree.children th) t′ (MapTree.children th) (node (MapTree.key t′) (MapTree.value t′) (proj₁ w))
-- detachNodesGo-preserves-pid x | just v | Eq.[ y ] | w | Eq.[ z ] | no _ | just u | just x₁ = {!!}
-- ... | nothing = {!!}
-- detachNodesGo-preserves-pid x | v | Eq.[ y ] | w | Eq.[ z ] | no _ | nothing = {!!}

-- pid≡rootPid : pid[ e ] ≡ rootPid treeClock[ e ]
-- pid≡rootPid {e = init} = refl
-- pid≡rootPid {e = send _ e} = pid≡rootPid {e = e}
-- pid≡rootPid {e = recv e e′} with rootPid treeClock[ e ] Fin.≟ rootPid treeClock[ e′ ] |  inspect (rootPid treeClock[ e ] Fin.≟_) (rootPid treeClock[ e′ ])
-- pid≡rootPid {e = recv e e′} | yes _ | _ with rootClk treeClock[ e ] <ᵇ rootClk treeClock[ e′ ] | inspect (rootClk treeClock[ e ] <ᵇ_) (rootClk treeClock[ e′ ])
-- pid≡rootPid {e = recv e e′} | yes _ | _ | true  | Eq.[ eq ] rewrite eq = pid≡rootPid {e = e′}
-- pid≡rootPid {e = recv e e′} | yes _ | Eq.[ eq ] | false | _ rewrite eq  with rootPid treeClock[ e′ ] Fin.≟ rootPid treeClock[ e ]
-- pid≡rootPid {e = recv e e′} | yes _ | _ | false | _   | yes z  = Eq.trans (pid≡rootPid {e = e′} ) z
-- pid≡rootPid {e = recv e e′} | yes x | _ | false | _   | no z   = ⊥-elim (z (Eq.sym x))
-- pid≡rootPid {e = recv e e′} | no  _ | _  with lookupNode.go (rootPid treeClock[ e ]) (rootPid treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) (MapTree.children treeClock[ e′ ])(MapTree.children treeClock[ e′ ]) 
-- pid≡rootPid {e = recv e e′} | no  _ | _          | just (c , _)  with rootClk treeClock[ e ] <ᵇ c  
-- pid≡rootPid {e = recv e e′} | no  _ | _          | just _       | true  = pid≡rootPid {e = e′}
-- pid≡rootPid {e = recv e e′} | no  _ |  Eq.[ eq ] | just _       | false rewrite eq with removeNode.go (rootPid treeClock[ e ]) (rootPid treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) (MapTree.children treeClock[ e′ ])(MapTree.children treeClock[ e′ ]) | getUpdatedNodesJoin.go (rootPid treeClock[ e ]) (rootClk treeClock[ e ]) (rootAclk treeClock[ e ]) (MapTree.children treeClock[ e ]) treeClock[ e′ ] (MapTree.children treeClock[ e ])
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | just _       | false | (z  , _) | [] with detachNodes.go (rootPid treeClock[ e ]) (MapTree.value treeClock[ e ]) [] treeClock[ e′ ] [] (node (rootPid  treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) z)
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | just _       | false | _  | _ | _ =  pid≡rootPid {e = e′}
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | just _       | false | (z  , _) | w ∷ ws with detachNodes w (node (rootPid  treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) z)
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | just _       | false | _  | _ | nothing = {!!}
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | just _       | false | _  | _ | just (node _ _ _)  =  {!!}
-- pid≡rootPid {e = recv e e′} | no  _ |  Eq.[ eq ] | nothing rewrite eq with removeNode.go (rootPid treeClock[ e ]) (rootPid treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) (MapTree.children treeClock[ e′ ])(MapTree.children treeClock[ e′ ]) | getUpdatedNodesJoin.go (rootPid treeClock[ e ]) (rootClk treeClock[ e ]) (rootAclk treeClock[ e ]) (MapTree.children treeClock[ e ]) treeClock[ e′ ] (MapTree.children treeClock[ e ])
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | nothing | (z  , _) | w with detachNodes.go (rootPid treeClock[ e ]) (MapTree.value treeClock[ e ]) w treeClock[ e′ ] w (node (rootPid  treeClock[ e′ ]) (MapTree.value treeClock[ e′ ]) z)
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | nothing | _ | _ | just (node k _ _) = {!!}
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | nothing | _ | w | nothing with rootPid treeClock[ e′ ] Fin.≟ rootPid treeClock[ e ] | removeNode.go (MapTree.key treeClock[ e′ ])(MapTree.key treeClock[ e ]) (MapTree.value treeClock[ e ]) w w
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | nothing | _ | _  | nothing | no _ | _ , nothing = pid≡rootPid {e = e′}
-- pid≡rootPid {e = recv e e′} | no  _ |  _         | nothing | _ | _  | nothing | no _ | _ ,  just (node k _ _) = {!!}
-- pid≡rootPid {e = recv e e′} | no  x |  _         | nothing | _ | _  | nothing | yes z | _ = ⊥-elim (x (Eq.sym z))

-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc : ∀ {pid eid n} {: Event pid eid}  → lookupClk pid[ e ] treeClock[ e ] ≡ just n →  lookupClk pid[ e ] (inc treeClock[ e ]) ≡ just (suc n)
-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc {e = e} _ with lookupClk pid[ e ] (treeClock[ e ]) | inspect (lookupClk pid[ e ])( treeClock[ e ]) 
-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc {pid = Fin.zero} e@{e = init} x  | just n | Eq.[ refl ]  = cong just (cong suc (just-injective x))
-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc {pid = Fin.zero} {e = send _ e} x  | just n | Eq.[ q ] = {!!}
-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc {pid = Fin.zero} {e = recv e e₁} x | _ | _ = {!!}
-- lookup-rootPid-inc∘tc≡suc∘lookup-rootPid-tc {pid = Fin.suc pid}  x | just n | Eq.[ q ]  = {!!}

-- _TC≺_ : ClockCompare
-- e TC≺ e′ = ∀{n} → e ≢ init × rootClk treeClock[ e ] ≤ lookupClk pid[ e ] treeClock[ e′] × e ≇ e′

-- open ⊏-PreservingRules

-- TC≺-⊏-Preserving : ⊏-PreservingRules _TC≺_
-- ⊏-preserving-rule₁ TC≺-⊏-Preserving {e = e} with lookupClk pid[ e ] (inc treeClock[ e ]) | inspect (lookupClk pid[ e ]) (inc treeClock[ e ])
-- ... | just x  | _  = {!!} , ({!!} , {!!})
-- ... | nothing | _ = {!!} , ({!!} , {!!})
-- ⊏-preserving-rule₂ TC≺-⊏-Preserving = {!!}
-- ⊏-preserving-rule₃ TC≺-⊏-Preserving = {!!}
-- ⊏-preserving-trans  TC≺-⊏-Preserving x y = {!!}
