\begin{code}
module NaturalProp where

open import Data.Nat as Nat hiding (_*_)
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Algebra.Structures
open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

+-comm = IsCommutativeMonoid.comm (IsCommutativeSemiring.+-isCommutativeMonoid isCommutativeSemiring)
-- Natural properties
lemmam≡n→m+1≤n+1 : {m n : ℕ} → n ≡ m → suc m ≤′ suc n
lemmam≡n→m+1≤n+1 {m} {.m} refl = ≤′-refl

lemman>0→n+1≤m+n : {m n : ℕ} → m > zero → suc n ≤′ m + n
lemman>0→n+1≤m+n {0}     {n} ()
lemman>0→n+1≤m+n {suc m} {n} 1≤m
  = ≤⇒≤′ (start
            suc n
            ≤⟨ s≤s (n≤m+n m n) ⟩
            suc (m + n)
            ≤⟨ ≤-refl ⟩
            suc m + n
          ◽)

lemmam>0→m+1≤m+n : {m n : ℕ} → n > zero → suc m ≤′ m + n
lemmam>0→m+1≤m+n {m} {n} 1≤n rewrite sym (+-comm n m) = lemman>0→n+1≤m+n {n} {m} 1≤n  
\end{code}
