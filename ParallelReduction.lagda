\begin{code}
module ParallelReduction where

open import Chi
open import Term renaming (_⊆_ to _⊆c_ ; _∈_ to _∈c_)
open import Substitution
open import SubstitutionLemmas
open import Alpha
open import Beta
open import Relation Λ hiding (_++_) renaming (_⊆_ to _⊆R_)

open import Function
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
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) hiding (trans)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Algebra.Structures
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infixl 3 _⇉_
infixl 3 _⇉ₛ_
\end{code}

Parallel reduction.

%<*parallel>
\begin{code}
data _⇉_ : Λ → Λ → Set where
  ⇉v : (x : V)                               → v x ⇉ v x
  ⇉ƛ : (x : V){M M' : Λ}  → M ⇉ M'           → ƛ x M ⇉ ƛ x M'
  ⇉· : {M M' N N' : Λ}    → M ⇉ M' → N ⇉ N'  → M · N ⇉ M' · N'
  ⇉β : (x : V){M M' N N' : Λ}
                          → M ⇉ M' → N ⇉ N'  → ƛ x M · N ⇉ M' ∙ ι ≺+ (x , N') 
  ⇉α : {M N N' : Λ}       → M ⇉ N → N ∼α N'  → M ⇉ N'
\end{code}
%</parallel>


Parallel substitution.

\begin{code}
_⇉ₛ_ : Σ → Σ → Set
σ ⇉ₛ σ' = (x : V) → σ x ⇉ σ' x
\end{code}

\begin{code}
lemma⇉s : {σ σ' : Σ}(x y : V) → σ ⇉ₛ σ' → σ ≺+ (x , v y) ⇉ₛ σ' ≺+ (x , v y)
lemma⇉s {σ} {σ'} x y σ⇉σ' z with x ≟ z 
... | yes  _ = ⇉v y
... | no   _ = σ⇉σ' z

-- -- Lemma 7
-- lemma⇉* : {x : V}{M N : Λ} → x * N → M ⇉ N → x * M 
-- lemma⇉*  {x} 
--          x*N'          (⇉α M⇉N N∼N')      
--   = lemma⇉* (lemmaM∼M'→free← N∼N' x x*N') M⇉N
-- lemma⇉*  (*·l x*N)     (⇉· M⇉N M'⇉N')     
--   = *·l (lemma⇉* x*N M⇉N)
-- lemma⇉*  (*·r x*N')    (⇉· M⇉N M'⇉N') 
--   = *·r (lemma⇉* x*N' M'⇉N')
-- lemma⇉*  *v (⇉v x)                 
--   = *v
-- lemma⇉*  (*ƛ x*N y≢x)  (⇉ƛ y M⇉N)   
--   = *ƛ (lemma⇉* x*N M⇉N) y≢x
-- lemma⇉*  {x} 
--          x*M'∙ι≺+yN'   (⇉β y {M} {M'} {N} {N'} M⇉N M'⇉N')  
--   with lemmafreeσ→ {x} {M'} x*M'∙ι≺+yN'
-- ... | z , z*M' , z*ι≺+yN'y
--   with y ≟ z
-- lemma⇉*  {x} 
--          x*M'∙ι≺+yN'   (⇉β y {M} {M'} {N} {N'} M⇉M' N⇉N')  
--     | .x , x*M' , *v
--     | no   y≢x  
--   = *·l (*ƛ (lemma⇉* x*M' M⇉M') y≢x)
-- lemma⇉*  {x} 
--          x*M'∙ι≺+yN'   (⇉β y {M} {M'} {N} {N'} M⇉M' N⇉N')  
--     | .y , y*M' , x*N'
--     | yes  refl  
--   = *·r (lemma⇉* x*N' N⇉N')

-- -- Corolary lemma 7
-- lemma⇉# : {x : V}{M N : Λ} → x # M → M ⇉ N → x # N
-- lemma⇉# {x} {M} {N} x#M M⇉N with x #? N 
-- ... | yes x#N   = x#N
-- ... | no  ¬x#N  = ⊥-elim ((lemma-free→¬# (lemma⇉* (lemma¬#→free ¬x#N) M⇉N)) x#M)
\end{code}

\begin{code}
⇉ρ : Reflexive _⇉_
⇉ρ {v x}    = ⇉v x
⇉ρ {M · N}  = ⇉· ⇉ρ ⇉ρ
⇉ρ {ƛ x M}  = ⇉ƛ x ⇉ρ
\end{code}

\begin{code}
lemma→α⊆⇉ : _→α_ ⊆R _⇉_
lemma→α⊆⇉ (inj₁ (ctxinj  (▹β {M} {N} {x}))) 
  = ⇉β x ⇉ρ ⇉ρ
lemma→α⊆⇉ (inj₁ (ctx·l   M→βN)) 
  = ⇉· (lemma→α⊆⇉ (inj₁ M→βN)) ⇉ρ
lemma→α⊆⇉ (inj₁ (ctx·r   M→βN))  
  = ⇉· ⇉ρ (lemma→α⊆⇉ (inj₁ M→βN)) 
lemma→α⊆⇉ (inj₁ (ctxƛ {x} M→βN))  
  = ⇉ƛ x (lemma→α⊆⇉ (inj₁ M→βN)) 
lemma→α⊆⇉ (inj₂ M~N)             
  = ⇉α ⇉ρ M~N
\end{code}

\begin{code}
lemma⇉⊆→α* :  _⇉_ ⊆R _→α*_
lemma⇉⊆→α* (⇉v x)             = refl
lemma⇉⊆→α* (⇉ƛ x M⇉N)         = abs-star (lemma⇉⊆→α* M⇉N)
lemma⇉⊆→α* (⇉· {M} {M'} {N} {N'} M⇉M' N⇉N')     
  = begin→ 
       M · N
     →⟨ app-star-l (lemma⇉⊆→α* M⇉M')  ⟩
       M' · N
     →⟨ app-star-r (lemma⇉⊆→α* N⇉N') ⟩
       M' · N'
     ▣ 
lemma⇉⊆→α* (⇉β x {M} {M'} {N} {N'} M⇉M' N⇉N')   
  =  begin→
       (ƛ x M) · N
     →⟨ app-star-l (abs-star (lemma⇉⊆→α* M⇉M'))  ⟩
       (ƛ x M') · N
     →⟨ app-star-r (lemma⇉⊆→α* N⇉N')   ⟩
       (ƛ x M') · N'
     →⟨ just (inj₁ ( ctxinj ▹β))  ⟩
       M' ∙ ι ≺+ (x , N')
     ▣ 
lemma⇉⊆→α* (⇉α {M} {N} {P} M⇉N N∼P)       
  =  begin→
       M
     →⟨ lemma⇉⊆→α* M⇉N ⟩
       N
     →⟨ just (inj₂ N∼P) ⟩
       P   
     ▣  
\end{code}

\begin{code}
lemma⇉# : {x : V}{M N : Λ} → x # M → M ⇉ N → x # N
lemma⇉# x#M M⇉N = lemma→α*# x#M (lemma⇉⊆→α* M⇉N) 

lemma⇉* : {x : V}{M N : Λ} → x * N → M ⇉ N → x * M
lemma⇉* = dual-#-* lemma⇉#
\end{code}

Parallel reduction

\begin{code}
lemma⇉#⇂ : {x x' y : V}{M M' : Λ}{σ σ' : Σ} → ƛ x M ⇉ ƛ x' M' → σ ⇉ₛ σ' → y #⇂ (σ , ƛ x M) → y #⇂ (σ' , ƛ x' M')
lemma⇉#⇂ {x} ƛxM⇉ƛx'M' σ⇉σ' y#⇂σ,ƛxM z z*ƛxM' = lemma⇉# (y#⇂σ,ƛxM z (lemma⇉* z*ƛxM' ƛxM⇉ƛx'M')) (σ⇉σ' z) 
\end{code}

%<*parallelsubstitutionlemma>
\begin{code}
lemma⇉  : {M M' : Λ}{σ σ' : Σ} 
        → M ⇉ M' → σ ⇉ₛ σ' 
        → M ∙ σ ⇉ M' ∙ σ'
\end{code}
%</parallelsubstitutionlemma>

\begin{code}
lemma⇉  (⇉v x)            σ⇉σ' 
  = σ⇉σ' x
lemma⇉  {ƛ .x M} {ƛ .x M'} {σ} {σ'}
        (⇉ƛ x M⇉M')       σ⇉σ' 
  = ⇉α (⇉ƛ y (lemma⇉ M⇉M'  (lemma⇉s x y σ⇉σ'))) 
                           (∼σ  (corollary4-2  {x} {y} {M'} {σ'} (lemma⇉#⇂ (⇉ƛ x M⇉M') σ⇉σ' y#⇂σ,ƛxM))) 
  where
  y = χ (σ , ƛ x M)
  y#⇂σ,ƛxM : y #⇂ (σ , ƛ x M)
  y#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
lemma⇉  (⇉· M⇉M' N⇉N')    σ⇉σ' 
  = ⇉· (lemma⇉ M⇉M' σ⇉σ') (lemma⇉ N⇉N' σ⇉σ')
lemma⇉  .{ƛ x M · N} .{M' ∙ ι ≺+ (x , N')} {σ} {σ'}
        (⇉β x {M} {M'} {N} {N'} M⇉M' N⇉N')  σ⇉σ' 
  = ⇉α (⇉β y (lemma⇉ M⇉M' (lemma⇉s x y σ⇉σ')) (lemma⇉ N⇉N' σ⇉σ')) lemma∼
  where
  y = χ (σ , ƛ x M)
  y#⇂σ,ƛxM : y #⇂ (σ , ƛ x M)
  y#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
  lemma∼ : (M' ∙ σ'  ≺+ (x , v y)) ∙  ι ≺+ (y , N' ∙ σ') ∼α (M' ∙ ι ≺+ (x , N')) ∙ σ'
  lemma∼ = begin 
             (M' ∙ σ'  ≺+ (x , v y)) ∙  ι ≺+ (y , N' ∙ σ')
           ∼⟨ corollary1SubstLemma (lemma⇉#⇂ (⇉ƛ x M⇉M') σ⇉σ' y#⇂σ,ƛxM) ⟩
              M' ∙ σ'  ≺+ (x , N' ∙ σ')
           ≈⟨ corollary1Prop7 {M'} {N'} {σ'} {x} ⟩
             (M' ∙ ι ≺+ (x , N')) ∙ σ'
           ∎
lemma⇉  (⇉α M⇉N N∼N')     σ⇉σ' 
  = ⇉α (lemma⇉ M⇉N σ⇉σ') (lemma-subst N∼N' (λ _ _ → ∼ρ)) 
\end{code}

\begin{code}
lemma∼α⇂ρ : ∀ {σ M} → σ ∼α σ ⇂ M
lemma∼α⇂ρ x _ =  ∼ρ

lemma⇉ₛρ : ∀ {σ} → σ ⇉ₛ σ
lemma⇉ₛρ {σ} x = ⇉ρ

lemma⇉ₛ≺+ : (x : V) {M N : Λ} {σ σ' : Σ} → M ⇉ N → σ ⇉ₛ σ' → σ ≺+ (x , M) ⇉ₛ σ' ≺+ (x , N)
lemma⇉ₛ≺+ x {M} {N} {σ} {σ'} red red' y with x ≟ y
lemma⇉ₛ≺+ x red red' .x | yes refl = red
... | no ¬p = red' y

corollary⇉ₛ≺+ : (x : V) {M N : Λ} → M ⇉ N → ι ≺+ (x , M) ⇉ₛ ι ≺+ (x , N)
corollary⇉ₛ≺+ x M⇉N = lemma⇉ₛ≺+ x M⇉N lemma⇉ₛρ
\end{code}
