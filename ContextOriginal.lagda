\begin{code}
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_ ; refl ; cong ; _≗_ ; sym ; trans ; inspect ; Reveal_is_) renaming ([_] to [_]i)
open PropEq.≡-Reasoning

module Context {K : Set}(D : Set)(_≟_ : Decidable (_≡_ {A = K}))(_≟d_ : Decidable (_≡_ {A = D}))(d : K → D) where

open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.List hiding (any;all)
open import Function
open import Data.List.Any hiding (map;tail)
open import Data.List.All renaming (map to mapAll) 
open import Data.Product renaming (map to map×)
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Maybe hiding (Any;All;map)
open import Relation.Nullary
private open module M≡  = Membership (PropEq.setoid (K × D)) using (_∈_ ; find) 
private open module M≡′ = Membership (PropEq.setoid (D × D)) hiding (_⊆_) renaming (_∈_ to _∈′_) 
\end{code}

\begin{code}
Context = List (K × D)

∅ : Context
∅ = []

dom : Context → List K
dom = map proj₁

_∈d_ : (k : K) → (ks : List K) → Dec (Any (_≡_ k) ks)
k ∈d ks = any (_≟_ k) ks

_〔_〕 : Context → K → Maybe D
[] 〔 _ 〕 = nothing
((k1 , d1) ∷ rs) 〔 k2 〕 with k1 ≟ k2
... | yes _ = just d1
... | no  _ = rs 〔 k2 〕

lemma〔〕 : {ctx : Context}{k : K}{d′ : D} 
          → ((k , d′) ∷ ctx) 〔 k 〕  ≡ just d′
lemma〔〕 {k = k}  with k ≟ k
... | yes refl = refl
... | no  k≢k  = ⊥-elim (k≢k refl) 

lemma〔〕′ : {ctx ctx′ : Context}{k : K}{d′ : D}
          → ((k , d′) ∷ ctx) 〔 k 〕  ≡ ((k , d′) ∷ ctx′) 〔 k 〕
lemma〔〕′ {k = k} with k ≟ k
... | yes refl = refl
... | no  k≢k  = ⊥-elim (k≢k refl) 

lemma〔〕∷≡ : {ctx ctx′ : Context}{k k′ : K}{d′ : D}
            → ctx 〔 k 〕  ≡ ctx′ 〔 k 〕
            → ((k′ , d′) ∷ ctx) 〔 k 〕  ≡ ((k′ , d′) ∷ ctx′) 〔 k 〕
lemma〔〕∷≡ {k = k} {k′ = k′} ctx〔k〕≡ctx′〔k〕 with k′ ≟ k
lemma〔〕∷≡ {k = k} {k′ = .k} ctx〔k〕≡ctx′〔k〕 | yes refl = refl 
lemma〔〕∷≡ {k = k} {k′ = k′} ctx〔k〕≡ctx′〔k〕 | no  _    = ctx〔k〕≡ctx′〔k〕 

lemma〔〕noth : {ctx : Context}{p : K × D}{k : K} → (p ∷ ctx) 〔 k 〕 ≡ nothing → ctx 〔 k 〕 ≡ nothing
lemma〔〕noth {ctx = ctx} {p = (k′ , d′)} {k = k} p∷ctx〔k〕≡nothing
  with k′ ≟ k 
lemma〔〕noth {ctx = ctx} {p = (.k , d′)} {k = k} ()
  | yes refl 
lemma〔〕noth {ctx = ctx} {p = (k′ , d′)} {k = k} p∷ctx〔k〕≡nothing
  | no   _   = p∷ctx〔k〕≡nothing 

_〈_〉 : Context → K → D
ctx 〈 k 〉 = maybe′ id (d k) (ctx 〔 k 〕)

_\\_ : Context → K →  Context
[] \\ _ = []
((p' , d') ∷ rctx) \\ k with p' ≟ k
...                    | yes _ = rctx \\ k     
...                    | no  _ = (p' , d') ∷ (rctx \\ k)

postulate
--  lemma\\〈〉⌉ : {ctx : Context}{k : K} → ctx 〈 k 〉 ≡ d k → (ctx \\ k) 〈 k 〉 ≡ d k
  lemma\\ : {ctx : Context}{k : K} → (ctx \\ k) 〈 k 〉 ≡ d k

_≺+_ : Context → K × D → Context
ctx ≺+ p = p ∷ ctx 

≁P : Context → Context → K → Set
≁P ctx1 ctx2 k = ctx1 〈 k 〉 ≡ d k ∨ ctx2 〈 k 〉 ≡ d k

_≁_ : (ctx1 ctx2 : Context) → Set
ctx1 ≁ ctx2 = (k : K) → ≁P ctx1 ctx2 k

≁Pd : (ctx ctx′ : Context)(k : K) → Dec (≁P ctx ctx′ k)
≁Pd ctx ctx′ k
  with ctx 〈 k 〉 ≟d d k
... | yes ctx〈k〉≡dk    = yes (inj₁ ctx〈k〉≡dk)
... | no  ctx〈k〉≢dk
    with ctx′ 〈 k 〉 ≟d d k
...   | yes ctx′〈k〉≡dk = yes (inj₂ ctx′〈k〉≡dk)
...   | no  ctx′〈k〉≢dk 
  = no (λ ctx〈k〉≡dk∨ctx′〈k〉≡dk → lemma ctx ctx′ k ctx〈k〉≢dk ctx′〈k〉≢dk ctx〈k〉≡dk∨ctx′〈k〉≡dk)
  where lemma : (ctx ctx′ : Context)(k : K) 
              → ctx 〈 k 〉 ≢ d k 
              → ctx′ 〈 k 〉 ≢ d k 
              → ctx 〈 k 〉 ≡ d k ∨ ctx′ 〈 k 〉 ≡ d k 
              → ⊥
        lemma ctx ctx′ k ctx〈k〉≢dk ctx′〈k〉≢dk (inj₁ ctx〈k〉≡dk)  = ⊥-elim (ctx〈k〉≢dk ctx〈k〉≡dk)
        lemma ctx ctx′ k ctx〈k〉≢dk ctx′〈k〉≢dk (inj₂ ctx′〈k〉≡dk) = ⊥-elim (ctx′〈k〉≢dk ctx′〈k〉≡dk)

lemmactx〔k〕≡justd′→k,d′∈cxt : {ctx : Context}{k : K}{d′ : D} 
                                  → ctx 〔 k 〕 ≡ just d′ 
                                  → (k , d′) ∈ ctx
lemmactx〔k〕≡justd′→k,d′∈cxt {ctx = []}          {k = k} {d′ = d′} ()
lemmactx〔k〕≡justd′→k,d′∈cxt {ctx = ((k′′ , d′′) ∷ ctx)} {k = k} {d′ = d′} p∷ctx〔k〕≡justd′ 
  with k′′ ≟ k
lemmactx〔k〕≡justd′→k,d′∈cxt {ctx = ((.k , .d′) ∷ ctx)}  {k = k} {d′ = d′} refl
  | yes refl = here refl
lemmactx〔k〕≡justd′→k,d′∈cxt {ctx = ((k′′ , d′′) ∷ ctx)} {k = k} {d′ = d′} p∷ctx〔k〕≡justd′ 
  | no  _    
  = there (lemmactx〔k〕≡justd′→k,d′∈cxt {ctx = ctx} {k = k} {d′ = d′} p∷ctx〔k〕≡justd′)

lemmactx〈k〉≢dk→∃d′,k,d′∈cxt : (ctx : Context)(k : K) 
                             → ctx 〈 k 〉 ≢ d k 
                             → ∃ (λ d′ → (k , d′) ∈ ctx)
lemmactx〈k〉≢dk→∃d′,k,d′∈cxt ctx k ctx〈k〉≢dk 
  with ctx 〔 k 〕 |  inspect (λ k′ → ctx 〔 k′ 〕) k
... | just d′′    |  [ ctx〔k〕≡justd′′ ]i 
  = d′′ , (lemmactx〔k〕≡justd′→k,d′∈cxt ctx〔k〕≡justd′′)
... | nothing     |  _                    
  = ⊥-elim (ctx〈k〉≢dk refl)

_≁d_ : (ctx ctx′ : Context) → Dec (ctx ≁ ctx′)
ctx ≁d ctx′ 
  with all (λ p → ≁Pd ctx ctx′ (proj₁ p)) ctx′
... | yes ∀k∈ctx′,ctx≁ctx′  =  yes (aux (lookup ∀k∈ctx′,ctx≁ctx′))  
  where aux : (∀ {p} → p ∈ ctx′ → ≁P ctx ctx′ (proj₁ p)) → ctx ≁ ctx′
        aux ∀p→p∈ctx→≁Pctxctx′proj₁p k 
          with ctx′ 〈 k 〉 ≟d d k
        ... | yes ctx′〈k〉≡dk = inj₂ ctx′〈k〉≡dk
        ... | no  ctx′〈k〉≢dk = ∀p→p∈ctx→≁Pctxctx′proj₁p (proj₂ (lemmactx〈k〉≢dk→∃d′,k,d′∈cxt ctx′ k ctx′〈k〉≢dk))
... | no  ¬∀k∈ctx′,ctx≁ctx′ = no (λ ∀k,ctx≁ctx′ → ⊥-elim (¬∀k∈ctx′,ctx≁ctx′ (tabulate (aux ∀k,ctx≁ctx′))))
  where aux : ctx ≁ ctx′ → ∀ {x} → x ∈ ctx′ → ≁P ctx ctx′ (proj₁ x)
        aux ctx≁ctx′ {x = x}  _ = ctx≁ctx′ (proj₁ x) 

_∪_ : Context → Context → Context
ctx1 ∪ ctx2 = foldr _∷_ ctx2 ctx1 

lemma∪〔〕noth : {ctx1 ctx2 : Context}{k : K} → ctx1 〔 k 〕 ≡ nothing → ctx2 〔 k 〕 ≡ (ctx1 ∪ ctx2) 〔 k 〕 
lemma∪〔〕noth {ctx1 = []}                {k = k} ctx1〔k〕≡noth = refl
lemma∪〔〕noth {ctx1 = (k′ , d′) ∷ rctx1} {k = k} ctx1〔k〕≡noth
  with k′ ≟ k 
lemma∪〔〕noth {ctx1 = (.k , d′) ∷ rctx1} {k = k} ()
  | yes refl 
lemma∪〔〕noth {ctx1 = (k′ , d′) ∷ rctx1} {k = k} ctx1〔k〕≡noth
  | no  _    = lemma∪〔〕noth {ctx1 = rctx1} {k = k} ctx1〔k〕≡noth 

lemma∪〔〕just : {ctx1 ctx2 : Context}{k : K}{d′ : D} → ctx1 〔 k 〕 ≡ just d′ → (ctx1 ∪ ctx2) 〔 k 〕 ≡ just d′
lemma∪〔〕just {ctx1 = []}                {k = k} {d′ = d′} ()
lemma∪〔〕just {ctx1 = (k′ , d″) ∷ rctx1} {k = k} {d′ = d′} ctx1〔k〕≡justd′ 
  with k′ ≟ k
lemma∪〔〕just {ctx1 = (.k , .d′) ∷ rctx1} {k = k} {d′ = d′} refl
  | yes refl = refl
lemma∪〔〕just {ctx1 = (k′ , d″) ∷ rctx1} {k = k} {d′ = d′} ctx1〔k〕≡justd′ 
  | no  _    = lemma∪〔〕just {ctx1 = rctx1} {k = k} {d′ = d′} ctx1〔k〕≡justd′  

-- lemma〔〕∪noth : {ctx ctx′ : Context}{k : K} → (ctx ∪ ctx′) 〔 k 〕 ≡ nothing → ctx 〔 k 〕 ≡ nothing
-- lemma〔〕∪noth = {! !}

aux∩ : Context → Context → K × D → Maybe (D × D)
aux∩ ctx1 ctx2 (k′ , d′) 
  = maybe′ (λ d′′ → (maybe′ (λ d′′′ → just (d′′′ , d′′)) nothing (ctx1 〔 k′ 〕))) nothing (ctx2 〔 k′ 〕)

_∩_ : Context → Context → List (D × D)
ctx1 ∩ ctx2 = gfilter (aux∩ ctx1 ctx2) ctx1

postulate
  lemma∩map : {ctx ctx′ : Context}(g : D → D)
              → (map (map× id g) ctx) ∩ (map (map× id g) ctx′) ≡ (map (map× g g) (ctx ∩ ctx′))


lemma∩′ : {ctx ctx′ ctx′′ : Context}{k : K}{d′ d′′ d′′′ : D} 
         → (k , d′′′) ∈ ctx′′ 
         → ctx  〔 k 〕 ≡ just d′ 
         → ctx′ 〔 k 〕 ≡ just d′′
         → (d′ , d′′) ∈′ gfilter (aux∩ ctx ctx′) ctx′′
lemma∩′ {ctx = ctx} {ctx′ = ctx′} {k = k} 
       (here refl) _ _
  with ctx 〔 k 〕 | ctx′ 〔 k 〕
lemma∩′ {ctx = ctx} {ctx′ = ctx′} {k = k} 
       (here refl) refl refl 
  |     just d′   | just d′′  
  = here refl 
lemma∩′ {ctx = ctx} {ctx′ = ctx′} {k = k} 
       (here refl) ()   _ 
  |     nothing   | _
lemma∩′ {ctx = ctx} {ctx′ = ctx′} {k = k} 
       (here refl) _    ()
  |     _         | nothing
lemma∩′ {ctx = ctx} {ctx′ = ctx′} {ctx′′ = (k′ , d′′′) ∷ tctx′′} {k = k} 
       (there {x = .(k′ , d′′′)} k,d′′′∈tctx) ctx〔k〕≡justd′ ctx′〔k〕≡justd′′ 
  with ctx′ 〔 k′ 〕
... | nothing = lemma∩′ {ctx = ctx} {ctx′ = ctx′} {ctx′′ = tctx′′} {k = k} k,d′′′∈tctx ctx〔k〕≡justd′ ctx′〔k〕≡justd′′  
... | just d1 
  with ctx  〔 k′ 〕 
... | nothing = lemma∩′ {ctx = ctx} {ctx′ = ctx′} {ctx′′ = tctx′′} {k = k} k,d′′′∈tctx ctx〔k〕≡justd′ ctx′〔k〕≡justd′′  
... | just d2 = there (lemma∩′ {ctx = ctx} {ctx′ = ctx′} {ctx′′ = tctx′′} {k = k} k,d′′′∈tctx ctx〔k〕≡justd′ ctx′〔k〕≡justd′′)             

-- lemma∩″ : {ctx ctx′ ctx″ : Context}{k : K}{d′ d″ d‴ : D} 
--          → ctx  〔 k 〕 ≡ just d′ 
--          → ctx′ 〔 k 〕 ≡ just d″
--          → (d′ , d″) ∈′ (gfilter (aux∩ ctx ctx′) ctx″
-- lemma∩″ = {! !}

lemma∩ : {ctx1 ctx2 : Context}{k : K}{d1 d2 : D}
         → ctx1 〔 k 〕 ≡ just d1 
         → ctx2 〔 k 〕 ≡ just d2
         → (d1 , d2) ∈′ (ctx1 ∩ ctx2)
lemma∩ {ctx1 = ctx1} {ctx2 = ctx2} ctx〔k〕≡justd′ ctx′〔k〕≡justd′′ = lemma∩′ {ctx = ctx1} {ctx′ = ctx2} {ctx′′ = ctx1} (lemmactx〔k〕≡justd′→k,d′∈cxt ctx〔k〕≡justd′) ctx〔k〕≡justd′ ctx′〔k〕≡justd′′

aux⊆ : Context → Context → (K × D) → Set
aux⊆ ctx1 ctx2 p = ctx1 〔 proj₁ p 〕 ≡ ctx2 〔 proj₁ p 〕

_⊆_ : Context → Context → Set
ctx1 ⊆ ctx2 = All (aux⊆ ctx1 ctx2) ctx1

lemma⊆ : {ctx1 ctx2 : Context}{k : K}{d′ : D} → ctx1 ⊆ ctx2 → ((k , d′) ∷ ctx1) ⊆ ((k , d′) ∷ ctx2)
lemma⊆ ctx1⊆ctx2 = lemma〔〕′ ∷ mapAll lemma〔〕∷≡ ctx1⊆ctx2

lemma⊆∪ : {ctx1 ctx2 : Context} → ctx1 ⊆ (ctx1 ∪ ctx2)
lemma⊆∪ {ctx1 = []}            {ctx2 = ctx2} = []
lemma⊆∪ {ctx1 = (k , d′) ∷ ps} {ctx2 = ctx2} 
  = lemma〔〕′ ∷ tail (lemma⊆ (lemma⊆∪ {ctx1 = ps} {ctx2 = ctx2})) 

-- postulate
--   lemma∪≡ : {ctx1 ctx2 : Context} 
--           → All (λ p → proj₁ p ≡ proj₂ p) (ctx1 ∩ ctx2) 
--           → All (λ p → proj₁ p ≡ proj₂ p) (ctx2 ∩ ctx1) 

lemma⊆∪₂′ : {ctx1 ctx2 ctx3 : Context} → All (λ p → proj₁ p ≡ proj₂ p) (gfilter (aux∩ ctx3 ctx1) ctx2) 
           → ((k : K) → ctx3 〔 k 〕 ≡ nothing → ctx2 〔 k 〕 ≡ nothing)
           → All (aux⊆ ctx3 (ctx1 ∪ ctx3)) ctx2
lemma⊆∪₂′ {ctx1 = ctx1} {ctx2 = []}                {ctx3 = ctx3} all≡ctx3∩ctx1 ctx3〔k〕≡noth→ctx2〔k〕≡noth = []
lemma⊆∪₂′ {ctx1 = ctx1} {ctx2 = (k′ , d′) ∷ tctx2} {ctx3 = ctx3} all≡ctx3∩ctx1 ctx3〔k〕≡noth→ctx2〔k〕≡noth
  with ctx1 〔 k′ 〕 | inspect (λ k → ctx1 〔 k 〕) k′ 
... | nothing       | [ ctx1〔k′〕≡nothing ]i 
  =  (lemma∪〔〕noth {ctx1 = ctx1} {ctx2 = ctx3} ctx1〔k′〕≡nothing) ∷ 
     lemma⊆∪₂′ {ctx1 = ctx1} {ctx2 = tctx2} {ctx3 = ctx3} all≡ctx3∩ctx1 
               (λ k → λ ctx3〔k〕≡noth → lemma〔〕noth (ctx3〔k〕≡noth→ctx2〔k〕≡noth k ctx3〔k〕≡noth))
... | just d1       | [ ctx1〔k′〕≡justd1  ]i
  with ctx3 〔 k′ 〕 | inspect (λ k → ctx3 〔 k 〕) k′
... | just d2       | [ ctx3〔k′〕≡justd2  ]i
  = trans (trans ctx3〔k′〕≡justd2 
                 (cong just 
                       (lookup all≡ctx3∩ctx1 (here refl))))
          (sym (lemma∪〔〕just {ctx1 = ctx1} {ctx2 = ctx3} ctx1〔k′〕≡justd1))             ∷ 
    lemma⊆∪₂′ {ctx1 = ctx1} {ctx2 = tctx2} {ctx3 = ctx3} (tail all≡ctx3∩ctx1) 
                      ((λ k → λ ctx3〔k〕≡noth → lemma〔〕noth (ctx3〔k〕≡noth→ctx2〔k〕≡noth k ctx3〔k〕≡noth)) )
... | nothing       | [ ctx3〔k′〕≡nothing ]i 
  with (trans (sym (ctx3〔k〕≡noth→ctx2〔k〕≡noth k′ ctx3〔k′〕≡nothing)) (lemma〔〕 {ctx = tctx2} {k = k′} {d′ = d′}))
... | ()

lemma⊆∪₂ : {ctx1 ctx2 : Context} → All (λ p → proj₁ p ≡ proj₂ p) (ctx2 ∩ ctx1) → ctx2 ⊆ (ctx1 ∪ ctx2)
lemma⊆∪₂ {ctx1 = ctx1} {ctx2 = ctx2} all≡ctx2∩ctx1 
  = lemma⊆∪₂′ {ctx1 = ctx1} {ctx2 = ctx2} {ctx3 = ctx2} all≡ctx2∩ctx1 (λ k → id)

-- es corlolario del anterior lemma !!!!
postulate
  lemma⊆∷ : {ctx : Context}{k : K}{d′ : D} → ctx 〔 k 〕 ≡ nothing → ctx ⊆ ((k , d′) ∷ ctx)

lemma⊆〔〕just : {ctx1 ctx2 : Context}{k : K}{d : D} 
               → ctx1 ⊆ ctx2 
               → ctx1 〔 k 〕 ≡ just d 
               → ctx2 〔 k 〕 ≡ just d
lemma⊆〔〕just ctx1⊆ctx2 ctx1〔k〕≡justd 
  = trans (sym (lookup ctx1⊆ctx2 (lemmactx〔k〕≡justd′→k,d′∈cxt ctx1〔k〕≡justd))) ctx1〔k〕≡justd

-- lemma⊆≺+-aux : {ctx1 ctx2 : Context}{k k' : K}{d d' : D} 
--                 → ctx1 ⊆ ctx2 
--                 → (k' , d') ∈  ctx1 ≺+ (k , d) 
--                 → (ctx1 ≺+ (k , d)) 〔 k' 〕 ≡ (ctx2 ≺+ (k , d)) 〔 k' 〕
-- lemma⊆≺+-aux {k = k} {k' = k'} ctx1⊆ctx2 k'd'∈ctx1≺+kd
--   with k ≟ k'
-- lemma⊆≺+-aux {k = k} {k' = .k} ctx1⊆ctx2 (here refl)
--   | no k≢k' = ⊥-elim (k≢k' refl) 
-- lemma⊆≺+-aux {k = k} {k' = k'} ctx1⊆ctx2 (there k'd'∈ctx1)
--   | no k≢k' = lookup ctx1⊆ctx2 k'd'∈ctx1 
-- lemma⊆≺+-aux {k = k} {k' = .k} ctx1⊆ctx2 kd∈ctx1≺+kd
--     | yes refl = refl 

-- este lemma es lemma⊆ !!!!!
-- lemma⊆≺+ : {ctx1 ctx2 : Context}{k : K}{d : D} 
--            → ctx1 ⊆ ctx2 
--            → (ctx1 ≺+ (k , d)) ⊆ (ctx2 ≺+ (k , d))
-- lemma⊆≺+ ctx1⊆ctx2 = tabulate (lemma⊆≺+-aux ctx1⊆ctx2) 

postulate
  lemma⊆≺+\\ : {ctx : Context}{k : K}{d : D} → ctx ⊆ ((ctx \\ k) ≺+ (k , ctx 〈 k 〉))
  lemma⊇≺+\\ : {ctx : Context}{k : K}{d : D} → ((ctx \\ k) ≺+ (k , ctx 〈 k 〉)) ⊆ ctx

lemmamap〔〕 : {ctx : Context}{k : K}{g : D → D} 
           → (map (map× id g) ctx) 〔 k 〕 ≡ maybe′ (just ∘′ g) nothing (ctx 〔 k 〕)
lemmamap〔〕 {ctx = []}               {k = k} {g = g} = refl
lemmamap〔〕 {ctx = ((k1 , d1) ∷ ps)} {k = k} {g = g} with k1 ≟ k
lemmamap〔〕 {ctx = ((.k , d1) ∷ ps)} {k = k} {g = g} | yes refl = refl
lemmamap〔〕 {ctx = ((k1 , d1) ∷ ps)} {k = k} {g = g} | no  k1≢k = lemmamap〔〕 {ctx = ps} {k = k} {g = g}

lemmamap〈〉 : {ctx : Context}{k : K}{g : D → D} 
           → d k ≡ g (d k) 
           → (map (map× id g) ctx) 〈 k 〉 ≡ g (ctx 〈 k 〉)
lemmamap〈〉 {ctx = ctx} {k = k} {g = g} dk≡gdk 
  with (map (map× id g) ctx) 〔 k 〕              | lemmamap〔〕 {ctx = ctx} {k = k} {g = g}
... | .(maybe′ (just ∘′ g) nothing (ctx 〔 k 〕)) | refl 
  with ctx 〔 k 〕
... | nothing = dk≡gdk 
... | just d1 = refl 

lemma≁θ-aux : (ctx : Context)(g : D → D)(k : K) 
        → d k ≡ g (d k) → ctx 〈 k 〉 ≡ d k 
        → (map (map× id g) ctx) 〈 k 〉 ≡ d k
lemma≁θ-aux ctx g k dk≡gdk ctx〈k〉≡dk =
         begin
            (map (map× id g) ctx) 〈 k 〉
         ≡⟨ lemmamap〈〉 {ctx = ctx} {k = k} {g = g} dk≡gdk ⟩
            g (ctx 〈 k 〉)
         ≡⟨ cong g ctx〈k〉≡dk ⟩
            g (d k)
         ≡⟨ sym dk≡gdk ⟩
            d k
         ∎

lemma≁θ : {ctx1 ctx2 : Context}(g : D → D) 
        → ((k : K) → d k ≡ g (d k)) 
        → ctx1 ≁ ctx2 
        → map (map× id g) ctx1 ≁ map (map× id g) ctx2
lemma≁θ {ctx1 = ctx1} {ctx2 = ctx2} g ∀k,dk≡gdk ctx1≁ctx2 k 
  with ∀k,dk≡gdk k | ctx1≁ctx2 k
... |     dk≡gdk   | inj₁ ctx1〈k〉≡dk 
  = inj₁ (lemma≁θ-aux ctx1 g k dk≡gdk ctx1〈k〉≡dk)
... |     dk≡gdk   | inj₂ ctx2〈k〉≡dk 
  = inj₂ (lemma≁θ-aux ctx2 g k dk≡gdk ctx2〈k〉≡dk)

-- este lema se puede hacer con foldrfusion !
lemma∪θ :  {ctx1 ctx2 : Context}(g : D → D) 
        → (map (map× id g) ctx1) ∪ (map (map× id g) ctx2) ≡ map (map× id g) (ctx1 ∪ ctx2)
lemma∪θ {ctx1 = []}           {ctx2 = ctx2} g = refl
lemma∪θ {ctx1 = (k , d) ∷ ps} {ctx2 = ctx2} g = 
        begin
          foldr (flip _≺+_) (map (map× id g) ctx2) (map (map× id g) ((k , d) ∷ ps))
        ≡⟨ cong (λ xs → ((map× id g) (k , d)) ∷ xs) (lemma∪θ {ctx1 = ps} {ctx2 = ctx2} g) ⟩
          ((map× id g) (k , d)) ∷ (map (map× id g) (foldr (flip _≺+_) ctx2 ps))
        ∎

lemmag : {ctx : Context}(g : D → D)(d1 : D) 
       → g d1 ≡ d1
       → All (λ p → proj₂ p ≡ d1) ctx 
       → All (λ p → proj₂ p ≡ d1) (map (map× id g) ctx)
lemmag {ctx = []}             g d1 gd1≡d1 []              = []
lemmag {ctx = (n , .d1) ∷ ps} g d1 gd1≡d1 (refl ∷ alld1ps) = gd1≡d1 ∷ (lemmag g d1 gd1≡d1 alld1ps)
\end{code}


