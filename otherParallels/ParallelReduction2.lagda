\begin{code}
module ParallelReduction2 where

open import Chi
open import Term renaming (_⊆_ to _⊆c_ ; _∈_ to _∈c_)
open import Substitution
open import Alpha

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
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Algebra.Structures
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infixl 2 _⇉_
infixl 2 _⇉ₛ_

infixl 5 _[_/_]

_[_/_] : Λ → V → Λ → Λ
M [ x / N ] = M ∙ ι ≺+ (x , N)
\end{code}

Parallel reduction.

\begin{code}
data _⇉_ : Λ → Λ → Set where
  ⇉v :  (x : V)                            → v x ⇉ v x
  ⇉· :  {M M' N N' : Λ}    
        → M ⇉ M' → N ⇉ N'                  → M · N ⇉ M' · N'
  ⇉ƛ :  (x y z : V){M M' : Λ} → z #  ƛ x M → z # ƛ y M'    
        → M [ x / v z ] ⇉ M' [ y / v z ]   → ƛ x M ⇉ ƛ y M'
  ⇉β :  (x y : V){M M' N N' : Λ} → y # ƛ x M
        → M [ x / v y ] ⇉ M' → N ⇉ N'      → ƛ x M · N ⇉ M' [ y / N' ]
  ⇉α : {M N N' : Λ} → M ⇉ N → N ∼α N'      → M ⇉ N'
\end{code}

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

-- Lemma 7
lemma⇉* : {x : V}{M N : Λ} → x * N → M ⇉ N → x * M 
lemma⇉*  x*x            (⇉v x)                 
  = x*x
lemma⇉*  (*·l x*N)     (⇉· M⇉N M'⇉N')     
  = *·l (lemma⇉* x*N M⇉N)
lemma⇉*  (*·r x*N')    (⇉· M⇉N M'⇉N') 
  = *·r (lemma⇉* x*N' M'⇉N')
lemma⇉*  {x} 
         x*N'          (⇉α M⇉N N∼N')      
  = lemma⇉* (lemmaM∼M'→free← N∼N' x x*N') M⇉N
lemma⇉*  {z}
         (*ƛ z*N y≢z)  (⇉ƛ x y u {M} {N} u#ƛxM u#ƛyN M[x/u]⇉N[y/u])   
  with lemma⇉* (lemmafreeσ← {z} {N} {ι ≺+ (y , v u)} (z , ( z*N , (x≢y→x*x[y/M] y≢z)))) M[x/u]⇉N[y/u]
... | z*M[x/u]
  with lemmafreeσ→ {z} {M} z*M[x/u]
... | r , r*M , z*r[x/u]
  with x ≟ r
lemma⇉*  {z}
         (*ƛ z*N y≢z)  (⇉ƛ x y .z {M} {N} z#ƛxM z#ƛyN M[x/z]⇉N[y/z])   
    | z*M[x/z]
    | .x , x*M , *v 
    | yes refl
  = ⊥-elim ((lemma-free→¬# (*ƛ z*N y≢z)) z#ƛyN) 
lemma⇉*  {z}
         (*ƛ z*N y≢z)  (⇉ƛ x y u {M} {N} u#ƛxM u#ƛyN M[x/u]⇉N[y/u])   
    | z*M[x/u]
    | .z , z*M , *v
    | no x≢z
  = *ƛ z*M x≢z
lemma⇉*  {z} 
         z*M'[y/N']    (⇉β x y {M} {M'} {N} {N'} y#ƛxM M[x/y]⇉M' N⇉N')  
  with lemmafreeσ→ {z} {M'} z*M'[y/N']
... | w , w*M' , z*w[y/N']
  with y ≟ w
lemma⇉*  {z} 
         y*M'[y/N']    (⇉β x y {M} {M'} {N} {N'} y#ƛxM M[x/y]⇉M' N⇉N')  
    | .y , y*M' , z*N'
    | yes refl
  = *·r (lemma⇉* z*N' N⇉N') 
lemma⇉*  {z} 
         z*M'[y/N']    (⇉β x y {M} {M'} {N} {N'} y#ƛxM M[x/y]⇉M' N⇉N')  
    | .z , z*M' , *v
    | no y≢z
  with lemmafreeσ→ {z} {M} (lemma⇉* z*M' M[x/y]⇉M')
... | u , u*M , z*u[x/y]
  with x ≟ u
lemma⇉*  .{y} 
         y*M'[y/N']    (⇉β x y {M} {M'} {N} {N'} y#ƛxM M[x/y]⇉M' N⇉N')  
    | .y , y*M' , *v
    | no y≢y
    | .x , x*M , *v
    | yes refl
  = ⊥-elim (y≢y refl)
lemma⇉*  {z} 
         z*M'[y/N']    (⇉β x y {M} {M'} {N} {N'} y#ƛxM M[x/y]⇉M' N⇉N')  
    | .z , z*M' , *v
    | no y≢z
    | .z , z*M , *v
    | no x≢z
  = *·l (*ƛ z*M x≢z)

-- Corolary lemma 7
lemma⇉# : {x : V}{M N : Λ} → x # M → M ⇉ N → x # N
lemma⇉# {x} {M} {N} x#M M⇉N with x #? N 
... | yes x#N   = x#N
... | no  ¬x#N  = ⊥-elim ((lemma-free→¬# (lemma⇉* (lemma¬#→free ¬x#N) M⇉N)) x#M)
\end{code}

\begin{code}
open import Induction.Nat
open import NaturalProp
--
⇉ρ≤ : (n : ℕ) 
  → ((y : ℕ) → suc y ≤′ n → (M : Λ) → y ≡ length M → M ⇉ M) 
  → (M : Λ) → n ≡ length M → M ⇉ M
⇉ρ≤ .(suc zero) rec (v x) refl 
  = ⇉v x
⇉ρ≤ .(length M + length N) rec (M · N) refl 
  = ⇉·  (rec (length M) (lemmam>0→m+1≤m+n (length>0 {N})) M refl) 
        (rec (length N) (lemman>0→n+1≤m+n (length>0 {M})) N refl)
⇉ρ≤ .(suc (length M)) rec (ƛ x M) refl 
  = ⇉ƛ  x x x #ƛ≡ #ƛ≡ 
        (rec (length (M ∙ (ι ≺+ (x , v x)))) 
             (lemmam≡n→m+1≤n+1 (lemma-length-corolary {x} {x} {M})) 
             (M ∙ (ι ≺+ (x , v x))) 
             refl)
--
⇉ρ : Reflexive _⇉_
⇉ρ {M} = (<-rec _ ⇉ρ≤) (length M) M refl
--
lemmaσ⇉σ : {σ : Σ} → σ ⇉ₛ σ
lemmaσ⇉σ x = ⇉ρ
\end{code}


