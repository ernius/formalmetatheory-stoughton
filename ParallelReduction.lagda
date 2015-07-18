\begin{code}
module ParallelReduction where

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
\end{code}

Parallel reduction.

\begin{code}
data _⇉_ : Λ → Λ → Set where
  ⇉v : (x : V)                               → v x ⇉ v x
  ⇉ƛ : (x : V){M M' : Λ}  → M ⇉ M'           → ƛ x M ⇉ ƛ x M'
  ⇉· : {M M' N N' : Λ}    → M ⇉ M' → N ⇉ N'  → M · N ⇉ M' · N'
  ⇉β : (x : V){M M' N N' : Λ}
                          → M ⇉ M' → N ⇉ N'  → ƛ x M · N ⇉ M' ∙ ι ≺+ (x , N') 
  ⇉α : {M N N' : Λ}
                          → M ⇉ N → N ∼α N'  → M ⇉ N'
\end{code}

Parallel substitution.

\begin{code}
_⇉ₛ_ : Σ → Σ → Set
σ ⇉ₛ σ' = (x : V) → σ x ⇉ σ' x
\end{code}

\begin{code}
postulate
  lemma⇉s : {σ σ' : Σ}(x y : V) → σ ⇉ₛ σ' → σ ≺+ (x , v y) ⇉ₛ σ' ≺+ (x , v y)
  lemma⇉* : {x : V}{M N : Λ} → x * N → M ⇉ N → x * M -- Lemma 7
  lemma⇉# : {x : V}{M N : Λ} → x # M → M ⇉ N → x # N -- corollary of lemma 7 ?
\end{code}
