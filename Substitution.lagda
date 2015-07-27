\begin{code}
module Substitution where

open import Chi
open import Term renaming (_⊆_ to _⊆c_ ; _∈_ to _∈c_)
open import ListProperties

open import Function renaming (_∘_ to _∘f_)
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse
import Function.Equality as FE
open import Data.List hiding (any) renaming (length to length') 
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open import Data.List.Any.Properties
open Any.Membership-≡ 
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Nat as Nat hiding (_*_)
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Empty
open import Data.Product renaming (Σ to Σₓ;map to mapₓ) 
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Algebra.Structures
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infixl 8 _≺+_
infix  5 _∙_ 
--infix 1 _≅_
\end{code}

Substitutions are functions from variables to terms.

\begin{code}
Σ = V → Λ
\end{code}

\begin{code}
ι : Σ 
ι = id ∘f v
\end{code}

\begin{code}
_≺+_ : Σ → V × Λ → Σ
(σ ≺+ (x , M)) y with x ≟ y
... | yes _ = M
... | no  _ = σ y
\end{code}



-- %<*sigmatype>
-- \begin{code}
-- data _∶_⇀_ : Σ → List V → List V → Set where
--   ∶⇀ι   :  {Γ Δ : List V} 
--         →  Γ ⊆ Δ → ι ∶ Γ ⇀ Δ
--   ∶⇀<+  :  {Γ Δ : List V}{M : Λ}{σ : Σ}(x : V) 
--         →  σ ∶ Γ ⇀ Δ 
--         →  Δ ⊢ M
--         →  σ <+ (x , M) ∶ Γ ‚ x ⇀ Δ
-- \end{code}
-- %</sigmatype>

%<*sigmatype>
\begin{code}
infix 1 _∶_⇀_⇂_
_∶_⇀_⇂_ : Σ → Cxt → Cxt → Λ → Set
σ ∶ Γ ⇀ Δ ⇂ M = {z : V} → z * M → (p : z ∈c Γ) → Δ ⊢ σ z ∶ Γ ⟨ p ⟩

infix 1 _∶_⇀_
_∶_⇀_ : Σ → Cxt → Cxt → Set
σ ∶ Γ ⇀ Δ = {z : V}(p : z ∈c Γ) → Δ ⊢ σ z ∶ Γ ⟨ p ⟩

lemma⇀ : {σ : Σ}{Γ Δ : Cxt}{M : Λ} → σ ∶ Γ ⇀ Δ → σ ∶ Γ ⇀ Δ ⇂ M 
lemma⇀ σ:Γ⇀Δ {z} _ z∈Γ = σ:Γ⇀Δ z∈Γ
\end{code}
%</sigmatype>

\begin{code}
lemmaι⇀ : {Γ : Cxt} → ι ∶ Γ ⇀ Γ
lemmaι⇀ z∈Γ = ⊢v z∈Γ
\end{code}

\begin{code}
lemmaι≺+⇀ : {Γ : Cxt}{α : Type}{x : V}{N : Λ} →  Γ ⊢ N ∶ α → (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ α) ⇀ Γ
lemmaι≺+⇀ Γ⊢N:α .{x}  (here {x , α} refl) 
  with x ≟ x
... | yes _   = Γ⊢N:α
... | no x≢x  = ⊥-elim (x≢x refl)
lemmaι≺+⇀ Γ⊢N:α {y}   (there {x ∶ α} y≢x y∈Γ)
  with x ≟ y 
... | yes x≡y = ⊥-elim (y≢x (sym x≡y))
... | no  _   = ⊢v y∈Γ
\end{code}



-- \begin{code}
-- lemmaWeakening:⇀ x (∶⇀ι Γ⊆Δ) = ∶⇀ι (there ∘ Γ⊆Δ) 
-- lemmaWeakening:⇀ x (∶⇀<+ y σ:Γ⇀Δ Δ⊢M) 
--   = ∶⇀<+ y (lemmaWeakening:⇀ x σ:Γ⇀Δ) (lemmaWeakening⊢ lemmaΓ⊆Γ,x Δ⊢M) 
-- \end{code}

Restriction of a substitution to a term.

\begin{code}
R = Σ × Λ
\end{code}

Freshness in a restriction is defined as follows:

\begin{code}
_#⇂_ : V → R → Set
x #⇂ (σ , M) = (y : V) → y * M → x # (σ y)
\end{code}


Free

\begin{code}
_*⇂_ : V → R → Set
x *⇂ (σ , M) = ∃ (λ y  → (y * M) × (x * σ y))
\end{code}

The right notion of identity of substitutions has to be formulated for restrictions:

\begin{code}
infix 1 _≅σ_
_≅σ_ : Σ → Σ → Set
σ ≅σ σ' = (x : V) → σ x ≡ σ' x

lemmaσ≺+x,x≅σ : {x : V} → ι ≺+ (x , v x) ≅σ ι
lemmaσ≺+x,x≅σ {x} y with x ≟ y
... | no   _     = refl
lemmaσ≺+x,x≅σ {x} .x
    | yes  refl  = refl

_≅⇂_ : R → R → Set
(σ , M) ≅⇂ (σ' , M') = (M ∼* M') × ((x : V) → x * M → σ x ≡ σ' x)

_≅_⇂_ : Σ → Σ → Λ → Set
σ ≅ σ' ⇂ M = (σ , M) ≅⇂ (σ' , M)

lemma≅≺+ : {x : V}{N : Λ}{σ σ' : Σ} → σ ≅σ σ' → σ ≺+ (x , N) ≅σ σ' ≺+ (x , N)
lemma≅≺+ {x} σ≌σ' y with x ≟ y
... | yes  _ = refl 
... | no   _ = σ≌σ' y

prop6 : {σ σ' : Σ}{M : Λ} → σ ≅σ σ' → σ ≅ σ' ⇂ M
prop6 σ≅σ' = ((λ _ → id) , (λ _ → id)) , λ x _ → σ≅σ' x
\end{code}

\begin{code}
_∼*⇂_ : R → R → Set
(σ , M) ∼*⇂ (σ' , M') =  ((x : V) → x *⇂ (σ , M) → x *⇂ (σ' , M')) × 
                         ((x : V) → x *⇂ (σ' , M') → x *⇂ (σ , M)) 
\end{code}

\begin{code}
fv : Λ → List V
fv (v a)     = [ a ]
fv (M · N)   = fv M ++ fv N
fv (ƛ a M)   = fv M - a
--
lemmafvfree→ : (x : V)(M : Λ) → x ∈ fv M → x * M
lemmafvfree→ x (v y)    (here x≡y) with y ≟ x 
... | no   y≢x = ⊥-elim (y≢x (sym x≡y)) 
lemmafvfree→ x (v .x)    (here x≡x) 
    | yes  refl = *v
lemmafvfree→ x (v y) (there ()) 
lemmafvfree→ x (M · N)  x∈fvMN with c∈xs++ys→c∈xs∨c∈ys  x∈fvMN 
... | inj₁ x∈fvM = *·l (lemmafvfree→ x M x∈fvM)
... | inj₂ x∈fvN = *·r (lemmafvfree→ x N x∈fvN)
lemmafvfree→ x (ƛ y M)  x∈fvM-y with y ≟ x | lemmafilter→ x (fv M) (λ z → not (⌊ y ≟ z ⌋)) x∈fvM-y
... | no y≢x   | _ , x∈fvM = *ƛ (lemmafvfree→ x M x∈fvM) y≢x 
lemmafvfree→ x (ƛ .x M)  x∈fvM-y 
    | yes refl | () , _  
-- 
lemmafvfree← : (x : V)(M : Λ) → x * M → x ∈ fv M
lemmafvfree← x (v .x)    *v             
  = here refl
lemmafvfree← x .(M · N)  (*·l {.x} {M} {N} xfreeM)     
  = c∈xs∨c∈ys→c∈xs++ys (inj₁ (lemmafvfree← x M xfreeM))
lemmafvfree← x .(M · N)  (*·r {.x} {M} {N} xfreeN)     
  = c∈xs∨c∈ys→c∈xs++ys {x} {fv M} (inj₂ (lemmafvfree← x N xfreeN))
lemmafvfree← x .(ƛ y M)  (*ƛ {.x} {y} {M} xfreeM y≢x)  
  = filter-∈ (λ z → not (⌊ y ≟ z ⌋)) (fv M) {x} (lemmafvfree← x M xfreeM) px≡true 
  where 
  px≡true : not ⌊ y ≟ x ⌋ ≡ true
  px≡true with y ≟ x
  ... | yes y≡x = ⊥-elim (y≢x y≡x)
  ... | no  _   = refl
\end{code}

\begin{code}
lemma∉fv→# : ∀ {a : V}{M : Λ} → a ∉ fv M → a # M
lemma∉fv→# {a} {M} a∉fvM with a #? M
... | yes a#M = a#M
... | no ¬a#M = ⊥-elim (a∉fvM (lemmafvfree← a M (lemma¬#→free ¬a#M)))
\end{code}

\begin{code}
f : {α : Type}(M : Λ)(Γ : Cxt) → Γ ⊢ M ∶ α → {x : V} → (x∈xs : x ∈ fv M) → V × Type
f M Γ Γ⊢M∶α = λ {x} x∈vs → (x , Γ ⟨ lemma⊢*∈ Γ⊢M∶α (lemmafvfree→ x M x∈vs) ⟩) 

freeCxt  : {Γ : Cxt}{M : Λ}{α : Type} 
         → Γ ⊢ M ∶ α
         → Cxt
freeCxt {Γ} {M} Γ⊢M∶α 
  = map-with-∈ (fv M) (f M Γ Γ⊢M∶α)

import Function.Equality as FE

lemmafreeCxt⊆  : {Γ : Cxt}{M : Λ}{α : Type} 
          → (p : Γ ⊢ M ∶ α)
          → freeCxt p ⊆c Γ
lemmafreeCxt⊆ {Γ} {M} Γ⊢M∶α {x} x∈free⊢ 
  with lemma∈→∈[] x∈free⊢ 
... | α , x,α∈free⊢ , free⊢⟨x∈free⊢⟩≡α 
  with FE.Π._⟨$⟩_ (from (map-with-∈↔ {f = f M Γ Γ⊢M∶α})) x,α∈free⊢
lemmafreeCxt⊆ {Γ} {M} Γ⊢M∶α {x} x∈free⊢ 
    | .(Γ ⟨ lemma⊢*∈ Γ⊢M∶α (lemmafvfree→ x M x∈fvM) ⟩) , x,α∈free⊢ , free⊢⟨x∈free⊢⟩≡Γ 
    | .x , x∈fvM , refl
  = lemma⊢*∈ Γ⊢M∶α (lemmafvfree→ x M x∈fvM) , free⊢⟨x∈free⊢⟩≡Γ 

lemmafreeCxt→*  : {Γ : Cxt}{M : Λ}{α : Type} 
           → (p : Γ ⊢ M ∶ α)
           → (x : V) → x ∈c freeCxt p 
           → x * M
lemmafreeCxt→* {Γ} {M} Γ⊢M∶α x x∈free⊢ 
  with lemma∈→∈[] x∈free⊢ 
... | α , x,α∈free⊢ , free⊢⟨x∈free⊢⟩≡α 
  with FE.Π._⟨$⟩_ (from (map-with-∈↔ {f = f M Γ Γ⊢M∶α})) x,α∈free⊢
lemmafreeCxt→* {Γ} {M} Γ⊢M∶α x x∈free⊢ 
    | .(Γ ⟨ lemma⊢*∈ Γ⊢M∶α (lemmafvfree→ x M x∈fvM) ⟩) , x,α∈free⊢ , free⊢⟨x∈free⊢⟩≡Γ 
    | .x , x∈fvM , refl
    = lemmafvfree→ x M x∈fvM

lemmafreeCxt←*  : {Γ : Cxt}{M : Λ}{α : Type}{x : V}
           → (p : Γ ⊢ M ∶ α)
           → x * M
           → x ∈c freeCxt p
lemmafreeCxt←* {Γ} {M} {α} {x} Γ⊢M∶α x*M 
  with lemmafvfree← x M x*M 
... | x∈fvM
  = lemma∈[]→∈ (FE.Π._⟨$⟩_ (to (map-with-∈↔ {f = f M Γ Γ⊢M∶α})) (x , x∈fvM , refl)) 

lemmaStrengthening⊢free  : {Γ : Cxt}{M : Λ}{α : Type} 
                         → (p : Γ ⊢ M ∶ α) → freeCxt p ⊢ M ∶ α
lemmaStrengthening⊢free (⊢v {x} x∈Γ) 
  rewrite lemma∈!⟨⟩ (lemma⊢*∈ (⊢v x∈Γ) (lemmafvfree→ x (v x) (here refl))) x∈Γ
  = ⊢v (here refl) 
lemmaStrengthening⊢free (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) 
  with lemmaStrengthening⊢free Γ⊢M∶α⟶β | lemmaStrengthening⊢free Γ⊢N∶α
... | freeM⊢M∶α⟶β | freeN⊢N∶α 
  = ⊢·  (lemmaWeakening⊢ lemmafreeM⊆freeMN freeM⊢M∶α⟶β) 
        (lemmaWeakening⊢ lemmafreeN⊆freeMN freeN⊢N∶α) 
  where
  lemmafreeM⊆freeMN : freeCxt Γ⊢M∶α⟶β ⊆c freeCxt (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) 
  lemmafreeM⊆freeMN {x} x∈freeM 
    with lemmafreeCxt⊆ Γ⊢M∶α⟶β x∈freeM | lemmafreeCxt⊆ (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (lemmafreeCxt←* (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (*·l (lemmafreeCxt→* Γ⊢M∶α⟶β x x∈freeM)))
  ... | x∈Γ , freeM⟨x∈freeM⟩≡Γ⟨x∈Γ⟩ | x∈Γ' , freeMN⟨x∈freeMN⟩≡Γ⟨x∈Γ'⟩ rewrite lemma∈!⟨⟩ x∈Γ x∈Γ'
    =     lemmafreeCxt←* (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (*·l (lemmafreeCxt→* Γ⊢M∶α⟶β x x∈freeM)) 
       ,  trans freeM⟨x∈freeM⟩≡Γ⟨x∈Γ⟩ (sym freeMN⟨x∈freeMN⟩≡Γ⟨x∈Γ'⟩)
  lemmafreeN⊆freeMN : freeCxt Γ⊢N∶α ⊆c freeCxt (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) 
  lemmafreeN⊆freeMN {x} x∈freeN 
    with lemmafreeCxt⊆ Γ⊢N∶α x∈freeN | lemmafreeCxt⊆ (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (lemmafreeCxt←* (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (*·r (lemmafreeCxt→* Γ⊢N∶α x x∈freeN)))
  ... | x∈Γ , freeN⟨x∈freeN⟩≡Γ⟨x∈Γ⟩ | x∈Γ' , freeMN⟨x∈freeMN⟩≡Γ⟨x∈Γ'⟩ rewrite lemma∈!⟨⟩ x∈Γ x∈Γ'
    =     lemmafreeCxt←* (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) (*·r (lemmafreeCxt→* Γ⊢N∶α x x∈freeN)) 
       ,  trans freeN⟨x∈freeN⟩≡Γ⟨x∈Γ⟩ (sym freeMN⟨x∈freeMN⟩≡Γ⟨x∈Γ'⟩)
lemmaStrengthening⊢free (⊢ƛ {y} {α} Γ,y:α⊢M∶β)
  with lemmaStrengthening⊢free Γ,y:α⊢M∶β
... | freeM⊢M∶β
  = ⊢ƛ (lemmaWeakening⊢ lemmafreeM⊆freeλyM freeM⊢M∶β)
  where 
  lemmafreeM⊆freeλyM : freeCxt Γ,y:α⊢M∶β ⊆c freeCxt (⊢ƛ Γ,y:α⊢M∶β) ‚ y , α
  lemmafreeM⊆freeλyM {x} x∈freeM 
    with lemmafreeCxt⊆ Γ,y:α⊢M∶β x∈freeM 
  ... | x∈Γ,y:α , freeM⟨x∈freeM⟩≡Γ,y:α⟨x∈Γ,y:α⟩ 
    with x ≟ y
  ... | no x≢y 
    with lemmafreeCxt⊆ (⊢ƛ Γ,y:α⊢M∶β) (lemmafreeCxt←* (⊢ƛ Γ,y:α⊢M∶β) (*ƛ (lemmafreeCxt→* Γ,y:α⊢M∶β x x∈freeM) (λ y≡x → ⊥-elim (x≢y (sym y≡x)))))
  lemmafreeM⊆freeλyM {x} x∈freeM 
      | here x≡y , freeM⟨x∈freeM⟩≡Γ,y:α⟨x∈Γ,y:α⟩ 
      | no x≢y 
      | x∈Γ , freeλyM⟨x∈freeƛyM⟩≡Γ⟨x∈Γ⟩
    = ⊥-elim (x≢y x≡y) 
  lemmafreeM⊆freeλyM {x} x∈freeM 
      | there _ x∈Γ' , freeM⟨x∈freeM⟩≡Γ⟨x∈Γ'⟩ 
      | no x≢y 
      | x∈Γ , freeλyM⟨x∈freeƛyM⟩≡Γ⟨x∈Γ⟩
      rewrite lemma∈!⟨⟩ x∈Γ x∈Γ'
    =     there x≢y (lemmafreeCxt←* (⊢ƛ Γ,y:α⊢M∶β) (*ƛ (lemmafreeCxt→* Γ,y:α⊢M∶β x x∈freeM) (λ y≡x → ⊥-elim (x≢y (sym y≡x)))))
       ,  trans freeM⟨x∈freeM⟩≡Γ⟨x∈Γ'⟩ (sym freeλyM⟨x∈freeƛyM⟩≡Γ⟨x∈Γ⟩)
  lemmafreeM⊆freeλyM .{y} y∈freeM
      | here refl , freeM⟨x∈freeM⟩≡α
      | yes refl =  here refl , freeM⟨x∈freeM⟩≡α
  lemmafreeM⊆freeλyM .{y} y∈freeM
      | there y≢y _ , freeM⟨x∈freeM⟩≡Γ,y:α⟨x∈Γ⟩ 
      | yes refl = ⊥-elim (y≢y refl)
\end{code}

Chi encapsulation

\begin{code}
χ : R → V
χ (σ , M) = χ' (concat (map (fv ∘f σ) (fv M)))
\end{code}

\begin{code}
χ-lemma2 : (σ : Σ)(M : Λ) → χ (σ , M) #⇂ (σ , M)
χ-lemma2 σ M y yfreeM with χ (σ , M) #? σ y
... | yes χσM#σy = χσM#σy
... | no ¬χσM#σy = ⊥-elim (χ∉concatmapfv∘σfvM χ∈concatmapfv∘σfvM)
  where
  -- Using lemma lemmaχaux∉ we know χ not in the list (concat (map (fv ∘ σ) (fv M))) passed
  χ∉concatmapfv∘σfvM : χ (σ , M) ∉ (concat (map (fv ∘f σ) (fv M)))
  χ∉concatmapfv∘σfvM = lemmaχaux∉ (concat (map (fv ∘f σ) (fv M)))
  -- y * M ⇒ y ∈ fv M
  y∈fvM : y ∈ fv M
  y∈fvM = lemmafvfree← y M yfreeM
  -- due to y ∈ fv M we have that fv (σ y) ∈ map (fv ∘ σ) (fv M)
  fvσy∈mapfv∘σfvM : fv (σ y) ∈ (map (fv ∘f σ) (fv M))
  fvσy∈mapfv∘σfvM = ((FE.Π._⟨$⟩_ (to (map-∈↔ {f = fv ∘f σ} {y = fv (σ y)} {xs = fv M}))) (y , y∈fvM , refl))
  -- we know ¬ χ # σ y ⇒ χ * (σ y), and then χ ∈ fv (σ y)
  χfreeσy : χ (σ , M) ∈ (fv (σ y))
  χfreeσy = lemmafvfree← (χ (σ , M)) (σ y) (lemma¬#→free ¬χσM#σy)
  -- χ ∈ fv (σ y) and fv (σ y) ∈ map (fv ∘ σ) (fv M) ⇒ χ ∈ concat (map (fv ∘f σ) (fv M))
  χ∈concatmapfv∘σfvM : χ (σ , M) ∈ (concat (map (fv ∘f σ) (fv M)))
  χ∈concatmapfv∘σfvM = (FE.Π._⟨$⟩_ (to (concat-∈↔ {x = χ (σ , M)} {xss = map (fv ∘f σ) (fv M)}))) (fv (σ y) ,  χfreeσy , fvσy∈mapfv∘σfvM)
--
χ-lemma4 :  (σ σ' : Σ)(M M' : Λ) → (σ , M) ∼*⇂ (σ' , M') →
            χ (σ , M) ≡ χ  (σ' , M')
χ-lemma4 σ σ' M M' (h1 , h2) 
  = lemmaχaux⊆ ((concat (map (fv ∘f σ) (fv M)))) (concat (map (fv ∘f σ') (fv M'))) lemma⊆ lemma⊇
  where
  lemma⊆ : ((concat (map (fv ∘f σ) (fv M)))) ⊆ (concat (map (fv ∘f σ') (fv M'))) 
  lemma⊆ {y} y∈concat 
    with (FE.Π._⟨$⟩_ (from (concat-∈↔ {x = y} {xss = map (fv ∘f σ) (fv M)}))) y∈concat 
  ... | xs , y∈xs , xs∈map 
    with (FE.Π._⟨$⟩_ (from ((map-∈↔ {y = xs} {xs = fv M})))) xs∈map
  lemma⊆ {y} y∈concat 
      | .(fv (σ x)) , y∈fvσx , fvσx∈map
      | x , x∈fvM , refl
    with lemmafvfree→ x M x∈fvM | lemmafvfree→ y (σ x) y∈fvσx
  ... | xfreeM | yfreeσx
    with h1 y (x , xfreeM , yfreeσx)
  ... | u , ufreeM' , yfreeσ'u 
    with lemmafvfree← u M' ufreeM' | lemmafvfree← y (σ' u) yfreeσ'u
  ... | u∈fvM' | y∈fvσ'u 
    with (FE.Π._⟨$⟩_ (to ((map-∈↔ {f = fv ∘f σ'} {y = fv (σ' u)} {xs = fv M'})))) (u , u∈fvM' , refl)
  ... | fvσ'u∈map 
     = (FE.Π._⟨$⟩_ (to (concat-∈↔ {x = y} {xss = map (fv ∘f σ') (fv M')}))) (fv (σ' u) , y∈fvσ'u , fvσ'u∈map) 
  lemma⊇ : (concat (map (fv ∘f σ') (fv M'))) ⊆ ((concat (map (fv ∘f σ) (fv M))))
  lemma⊇ {y} y∈concat
    with (FE.Π._⟨$⟩_ (from (concat-∈↔ {x = y} {xss = map (fv ∘f σ') (fv M')}))) y∈concat 
  ... | xs , y∈xs , xs∈map 
    with (FE.Π._⟨$⟩_ (from ((map-∈↔ {y = xs} {xs = fv M'})))) xs∈map
  lemma⊇ {y} y∈concat 
      | .(fv (σ' x)) , y∈fvσ'x , fvσ'x∈map
      | x , x∈fvM' , refl
    with lemmafvfree→ x M' x∈fvM' | lemmafvfree→ y (σ' x) y∈fvσ'x
  ... | xfreeM' | yfreeσ'x
    with h2 y (x , xfreeM' , yfreeσ'x)
  ... | u , ufreeM , yfreeσu 
    with lemmafvfree← u M ufreeM | lemmafvfree← y (σ u) yfreeσu
  ... | u∈fvM | y∈fvσu 
    with (FE.Π._⟨$⟩_ (to ((map-∈↔ {f = fv ∘f σ} {y = fv (σ u)} {xs = fv M})))) (u , u∈fvM , refl)
  ... | fvσu∈map 
     = (FE.Π._⟨$⟩_ (to (concat-∈↔ {x = y} {xss = map (fv ∘f σ) (fv M)}))) (fv (σ u) , y∈fvσu , fvσu∈map) 
--
χ-lemma3 : (σ σ' : Σ)(M M' : Λ) → 
   (∀ x → x * M → σ x ∼* σ' x)   → 
   M ∼* M' → 
   χ (σ , M) ≡ χ  (σ' , M')
χ-lemma3 σ σ' M M' x*M⇛σx∼σ'x (*M⇒M' , *M'⇒M) = χ-lemma4 σ σ' M M' (h1 , h2)
  where 
  h1 : (y : V) → ∃ (λ x → (x * M)  × (y * σ x))  → ∃ (λ u → (u * M') ×  (y * σ' u))
  h1 y (x , x*M , y*σx)    =  x , *M⇒M' x x*M , proj₁ (x*M⇛σx∼σ'x x x*M) y y*σx
  h2 : (y : V) → ∃ (λ x → (x * M') × (y * σ' x)) → ∃ (λ u → (u * M) ×  (y * σ u)) 
  h2 y (x , x*M' , y*σ'x)  =  x , *M'⇒M x x*M' , proj₂ (x*M⇛σx∼σ'x x (*M'⇒M x x*M')) y y*σ'x
\end{code}

\begin{code}
_∙_ : Λ → Σ → Λ
v x    ∙ σ = σ x
M · N  ∙ σ = (M ∙ σ) · (N ∙ σ)
ƛ x M  ∙ σ = ƛ y (M ∙ (σ ≺+ (x , v y)))
  where y = χ (σ , ƛ x M)
\end{code}

\begin{code}
infixl  7 _∘_
_∘_ : Σ → Σ → Σ
(σ ∘ σ') x = (σ' x) ∙ σ

lemmaι : {σ : Σ} → σ ≅σ σ ∘ ι
lemmaι x = refl
\end{code}

\begin{code}
prop7 : {x : V}{σ σ' : Σ}{M : Λ} → (σ' ∘ σ) ≺+ (x , M ∙ σ') ≅σ σ' ∘ (σ ≺+ (x , M))
prop7 {x} {σ} {σ'} {M} y with x ≟ y
... | yes _  = refl
... | no _   = refl

\end{code}




\begin{code}
lemmax∙ι≺+x,N : (x : V)(N : Λ) → v x ∙ ι ≺+ (x , N) ≡ N  
lemmax∙ι≺+x,N x N with x ≟ x 
... | yes  _    = refl
... | no   x≢x  = ⊥-elim (x≢x refl) 
\end{code}

\begin{code}
lemma#→free# : {x : V}{σ : Σ}{M : Λ} → x # (M ∙ σ) → (y : V) → y * M → x # (σ y)
lemma#→free# {x} {σ} {v .y}   x#σy           y *v
  = x#σy
lemma#→free# {x} {σ} {M · N} (#· x#Mσ x#Nσ) y (*·l yfreeMσ)   
  = lemma#→free# x#Mσ y yfreeMσ
lemma#→free# {x} {σ} {M · N} (#· x#Mσ x#Nσ) y (*·r yfreeNσ)   
  = lemma#→free# x#Nσ y yfreeNσ
lemma#→free# .{χ (σ , ƛ z M)} {σ} {ƛ z M} #ƛ≡      y yfreeλzM
  = (χ-lemma2 σ (ƛ z M)) y yfreeλzM    
lemma#→free# {x} {σ} {ƛ z M} (#ƛ x#Mσ<+zw)  y (*ƛ yfreeM z≢y) 
  with z ≟ y | lemma#→free# x#Mσ<+zw y yfreeM
... | yes z≡y | _  = ⊥-elim (z≢y z≡y) 
... | no  _   | hi = hi 

sym≢ : {x y : V} → x ≢ y → y ≢ x
sym≢ {x} {y} x≢y y≡x = x≢y (sym y≡x)

lemmafree#→# : {x : V}{σ : Σ}{M : Λ} → ((y : V) → y * M → x # (σ y)) → x # (M ∙ σ) 
lemmafree#→# {x} {σ} {v y}   f = f y *v
lemmafree#→# {x} {σ} {M · N} f 
  = #· (lemmafree#→# (λ y yfreeM → f y (*·l yfreeM))) 
       (lemmafree#→# (λ y yfreeN → f y (*·r yfreeN)))
lemmafree#→# {x} {σ} {ƛ y M} f
  with χ (σ , ƛ y M) | x ≟ χ (σ , ƛ y M) | χ-lemma2 σ (ƛ y M) 
... | .x | yes refl | x#σ⇂λyM  = #ƛ≡
... | z  | no x≢z   | z#σ⇂λyM  = #ƛ (lemmafree#→# {x} {σ = σ ≺+ (y , v z)} {M} lemma)
   where lemma : (w : V) → w * M → x # (σ ≺+ (y , v z)) w
         lemma w wfreeM with y ≟ w 
         ... | yes _  = #v (sym≢ x≢z)
         ... | no y≢w = f w (*ƛ wfreeM y≢w)

lemmafree#y→# : {x : V}{M : Λ} → ((y : V) → y * M → x # v y) → x # M
lemmafree#y→# {x} {v y}   f = f y *v
lemmafree#y→# {x} {M · N} f 
  = #· (lemmafree#y→# (λ y yfreeM → f y (*·l yfreeM))) 
       (lemmafree#y→# (λ y yfreeN → f y (*·r yfreeN)))
lemmafree#y→# {x} {ƛ y M} f with x ≟ y
lemmafree#y→# {x} {ƛ y M} f 
    | no  x≢y = #ƛ (lemmafree#y→# lemma)
  where
  lemma : (u : V) → u * M → x # v u
  lemma u ufreeM with y ≟ u 
  ... | yes y≡u = #v (λ u≡x → x≢y (trans (sym u≡x) (sym y≡u)))
  ... | no  y≢u = f u (*ƛ ufreeM y≢u)
lemmafree#y→# {x} {ƛ .x M} f 
    | yes refl = #ƛ≡ 
\end{code}

No Capture Lemma

\begin{code}
lemmafreeσ→ : {x : V}{M : Λ}{σ : Σ} → x * (M ∙ σ) → ∃ (λ y → (y * M) × (x * σ y))
lemmafreeσ→ {x} {v z}   {σ} xfreeσz = z , *v , xfreeσz
lemmafreeσ→ {x} {M · N} {σ} (*·l xfreeMσ) = y , *·l yfreeMσ , xfreeσy
  where y = proj₁ (lemmafreeσ→ {x} {M} xfreeMσ)
        yfreeMσ = proj₁ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ))
        xfreeσy = proj₂ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ))
lemmafreeσ→ {x} {M · N} {σ} (*·r xfreeNσ) = y , *·r yfreeNσ , xfreeσy
  where y = proj₁ (lemmafreeσ→ {x} {N} xfreeNσ)
        yfreeNσ = proj₁ (proj₂ (lemmafreeσ→ {x} {N} xfreeNσ))
        xfreeσy = proj₂ (proj₂ (lemmafreeσ→ {x} {N} xfreeNσ))
lemmafreeσ→ {x} {ƛ y M} {σ} (*ƛ xfreeMσ<+yz z≢x)  
  with  χ (σ , ƛ y M) | proj₁ (lemmafreeσ→ {x} {M} xfreeMσ<+yz) 
    | proj₁ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ<+yz)) 
    | proj₂ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ<+yz))
... | z | w | wfreeM | xfreeσ<+yzw  with y ≟ w
... | no  y≢w =  w , *ƛ wfreeM y≢w , xfreeσ<+yzw 
... | yes y≡w with xfreeσ<+yzw
lemmafreeσ→ {x} {ƛ y M} {σ} (*ƛ xfreeMσ<+yz z≢x)  
    | .x | w | wfreeM | _
    | yes y≡w
    | *v = ⊥-elim (z≢x refl)
--
lemmafreeσ← : {x : V}{M : Λ}{σ : Σ} → x *⇂ (σ , M) → x * (M ∙ σ) 
lemmafreeσ← {x} {v z}   {σ} (.z , *v       , xfreeσz) = xfreeσz
lemmafreeσ← {x} {M · N} {σ} (y  , *·l yfreeM    , xfreeσy) = *·l (lemmafreeσ← (y , yfreeM , xfreeσy))
lemmafreeσ← {x} {M · N} {σ} (y  , *·r yfreeN    , xfreeσy) = *·r (lemmafreeσ← (y , yfreeN , xfreeσy))
lemmafreeσ← {x} {ƛ z M} {σ} (y  , *ƛ yfreeM z≢y , xfreeσy)
  with χ (σ , ƛ z M) | (χ-lemma2 σ (ƛ z M)) y (*ƛ yfreeM z≢y)
... | w | w#σy with w ≟ x
... | no  w≢x = *ƛ (lemmafreeσ← (y , yfreeM , lemma)) w≢x
  where lemma :  x * ((σ ≺+ (z , v w)) y)
        lemma with z ≟ y 
        ... | yes z≡y = ⊥-elim (z≢y z≡y)
        ... | no  _   = xfreeσy
lemmafreeσ← {x} {ƛ z M} {σ} (y  , *ƛ yfreeM z≢y , xfreeσy) 
  | .x | x#σy | yes refl = ⊥-elim ((lemma-free→¬# xfreeσy) x#σy)
\end{code}


\begin{code}
lemmaz*Mι≺+x,y→z≢x : {x y z : V}{M : Λ} → y ≢ z → z * M ∙ ι ≺+ (x , v y) → z ≢ x
lemmaz*Mι≺+x,y→z≢x {x} {y}  .{x} {M} y≢x x*Mι≺+x,y refl 
  with lemmafreeσ→ {x} {M} {ι ≺+ (x , v y)} x*Mι≺+x,y 
... | w , w*M , x*ι≺+x,yw 
  with x ≟ w
lemmaz*Mι≺+x,y→z≢x {x} {y}  .{x} {M} y≢x x*Mι≺+x,y refl 
    | .x , x*M , *v
    | no   x≢x   = ⊥-elim (x≢x refl)
lemmaz*Mι≺+x,y→z≢x {x} .{x} .{x} {M} x≢x x*Mι≺+x,x refl 
    | .x , x*M , *v
    | yes  refl  = ⊥-elim (x≢x refl)

lemmaι≺+⇀y  : {Γ : Cxt}{α : Type}{x y : V}{M : Λ}
            → ι ≺+ (y , v x) ∶ (Γ ‚ y ∶ α) ⇀ (Γ ‚ x ∶ α) ⇂ M ∙ ι ≺+ (x , v y)
lemmaι≺+⇀y  {x = x} {y} {M}  .{y}  z*M∙ι≺+x,y (here refl) 
  with y ≟ y
... | yes  _    = ⊢v (here refl)
... | no   y≢y  = ⊥-elim (y≢y refl)
lemmaι≺+⇀y  {x = x} {y} {M}  {z}   z*M∙ι≺+x,y (there z≢y z∈Γ) 
  with y ≟ z
... | yes  y≡z  = ⊥-elim (z≢y (sym y≡z))
... | no   y≢z  = lemmaWeakening⊢# (#v (lemmaz*Mι≺+x,y→z≢x {x} {y} {z} {M} y≢z z*M∙ι≺+x,y)) (lemmaι⇀  z∈Γ) 
\end{code}


\begin{code}
lemma-subst-σ≡ : {M : Λ}{σ σ' : Σ} → 
   (σ , M) ≅⇂ (σ' , M) → (M ∙ σ) ≡ (M ∙ σ')  
lemma-subst-σ≡ {v x}   {σ} {σ'} (_ , f) 
  = f x *v
lemma-subst-σ≡ {M · N} {σ} {σ'} (_ , f) 
  = cong₂ _·_
          (lemma-subst-σ≡ {M} (((λ _ x → x) , (λ _ x → x)) , (λ x xfreeM → f x (*·l xfreeM)))) 
          (lemma-subst-σ≡ {N} (((λ _ x → x) , (λ _ x → x)) , (λ x xfreeN → f x (*·r xfreeN))))
lemma-subst-σ≡ {ƛ x M} {σ} {σ'} (_ , f)
  with χ (σ , ƛ x M) | χ (σ' , ƛ x M) | 
       χ-lemma3 σ σ' (ƛ x M) (ƛ x M) (λ x x*M → (lemma-1 x x*M) , (lemma-2 x x*M)) ((λ _ → id) , (λ _ → id)) 
  where 
  lemma-1 : (w : V) → w * ƛ x M → (z : V) → z * σ w → z * σ' w
  lemma-1 w wfreeλxM z zfreeσw rewrite f w wfreeλxM = zfreeσw
  lemma-2 : (w : V) → w * ƛ x M → (z : V) → z * σ' w → z * σ w
  lemma-2 w wfreeλxM z zfreeσ'w rewrite f w wfreeλxM = zfreeσ'w
... | y | .y | refl 
  = cong (λ M → ƛ y M) (lemma-subst-σ≡ {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} (((λ _ x → x) , (λ _ x → x)) , lemma)) 
  where 
  lemma : ((z : V) → z * M → (σ ≺+ (x , v y)) z ≡ (σ' ≺+ (x , v y)) z)
  lemma z zfreeM with x ≟ z 
  ... | yes _   = refl
  ... | no  x≢z = f  z (*ƛ zfreeM x≢z) 
\end{code}

\begin{code}
lemma-length : {M : Λ}{σ : Σ} → ((w : V) → length (σ w) ≡ 1) → length M ≡ length (M ∙ σ)
lemma-length {v x}   {σ} p rewrite p x  = refl
lemma-length {M · N} {σ} p
  = cong₂ _+_ (lemma-length {M} {σ} p) (lemma-length {N} {σ} p)
lemma-length {ƛ z M} {σ} p with χ (σ , ƛ z M) 
... | w = cong (λ x → suc x) (lemma-length {M} {σ ≺+ (z , v w)} lemma)
  where
  lemma : (u : V) → length ((σ ≺+ (z , v w)) u) ≡ 1
  lemma u with z ≟ u 
  ... | yes _ = refl
  ... | no  _ = p u

lemma-length-corolary : {x y : V}{M : Λ} → length M ≡ length (M ∙ (ι ≺+ (x , v y)))
lemma-length-corolary {x} {y} {M} = lemma-length {M} {ι ≺+ (x , v y)} lemma
  where 
  lemma : (w : V) → length ((ι ≺+ (x , v y)) w) ≡ 1
  lemma w with x ≟ w 
  ... | yes _ = refl
  ... | no  _ = refl
\end{code}


%<*typesusbstterm>
\begin{code}
lemma⊢σM  :  {σ : Σ}{Γ Δ : Cxt}{M : Λ}{α : Type}
          →  Γ ⊢ M ∶ α → σ ∶ Γ ⇀ Δ ⇂ M → Δ ⊢ M ∙ σ ∶ α
\end{code}
%</typesusbstterm>

\begin{code}
lemma⊢σM  (⊢v p∈)              σ∶Γ⇀Δ⇂M
  = σ∶Γ⇀Δ⇂M *v p∈
lemma⊢σM  (⊢· Γ⊢M∶α⟶β Γ⊢N∶β)  σ∶Γ⇀Δ⇂M
  = ⊢·  (lemma⊢σM Γ⊢M∶α⟶β (λ {z} z*M z∈Γ → σ∶Γ⇀Δ⇂M (*·l z*M) z∈Γ)) 
        (lemma⊢σM Γ⊢N∶β (λ {z} z*M z∈Γ → σ∶Γ⇀Δ⇂M (*·r z*M) z∈Γ))
lemma⊢σM  {σ} {Σ} {Δ} {M = ƛ y M} {α = α ⟶ β} 
          Γ⊢ƛyM∶α⟶β           σ∶Γ⇀Δ⇂M
  with  freeCxt Γ⊢ƛyM∶α⟶β 
  |     lemmafreeCxt→* Γ⊢ƛyM∶α⟶β 
  |     lemmaStrengthening⊢free Γ⊢ƛyM∶α⟶β 
  |     lemmafreeCxt⊆ Γ⊢ƛyM∶α⟶β
... | Γ' | Γ'* | ⊢ƛ Γ',y:α⊢M∶β | Γ'⊆Γ
  = ⊢ƛ (lemma⊢σM {σ ≺+ (y , v x)} {Γ' ‚ y ∶ α} {Δ ‚ x ∶ α} Γ',y:α⊢M∶β lemmaaux⇀)
  where 
  x = χ (σ , ƛ y M)
  χ#⇂σƛxM = χ-lemma2 σ (ƛ y M)
  lemmaaux⇀ : (σ ≺+ (y , v x)) ∶ Γ' ‚ y , α ⇀ (Δ ‚ x , α) ⇂ M
  lemmaaux⇀ {z} z*M z∈Γ',x with y ≟ z
  lemmaaux⇀ {z} z*M (there _ z∈Γ')
    | no  y≢z  with Γ'⊆Γ z∈Γ'
  ... | z∈Γ , Γ'⟨z∈Γ'⟩≡Γ⟨z∈Γ⟩ 
    rewrite Γ'⟨z∈Γ'⟩≡Γ⟨z∈Γ⟩ 
    = lemmaWeakening⊢# (χ#⇂σƛxM z (Γ'* z z∈Γ')) (σ∶Γ⇀Δ⇂M (*ƛ z*M y≢z) z∈Γ)
  lemmaaux⇀ {z} z*M (here z≡y)
    | no  y≢z   = ⊥-elim (y≢z (sym z≡y))
  lemmaaux⇀ .{y} z*M (here _) 
    | yes refl  = ⊢v (here refl)
  lemmaaux⇀ .{y} z*M (there y≢y _)
    | yes refl  = ⊥-elim (y≢y refl)
\end{code}

