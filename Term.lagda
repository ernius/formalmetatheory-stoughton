\begin{code}
module Term where

open import NaturalProp
open import ListProperties
open import Chi

open import Data.Nat as Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Empty
open import Function
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse
import Function.Equality as FE
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ;_,_ to _∶_) public
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Data.List hiding (any) renaming (length to length') 
-- open import Data.List.Any as Any hiding (map)
-- open import Data.List.Any.Membership
-- open Any.Membership-≡ 
open import Algebra.Structures
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infix 6 _·_ 
infix 1 _⊢_∶_ 
infix 3 _#_ 
infix 1 _*_ 
\end{code}

\end{code}

%<*term>
\begin{code}
data Λ : Set where
  v    : V → Λ 
  _·_  : Λ → Λ → Λ 
  ƛ    : V → Λ → Λ 
\end{code}
%</term>

\begin{code}
data Type : Set where
  τ    : Type
  _⟶_  : Type → Type → Type
import Context
open module M = Context (Type)(_≟_) public
\end{code}

%<*type>
\begin{code}
data _⊢_∶_ (Γ : Cxt): Λ → Type → Set where
  ⊢v : {x : V}                     → (p∈ : x ∈ Γ)                → Γ ⊢ v x ∶ Γ ⟨ p∈ ⟩
  ⊢· : {α β : Type}{M N : Λ}       → Γ ⊢ M ∶ α ⟶ β → Γ ⊢ N ∶ α  → Γ ⊢ M · N ∶ β
  ⊢ƛ : {x : V}{α β : Type}{M : Λ}  → Γ ‚ x ∶ α ⊢ M ∶ β           → Γ ⊢ ƛ x M ∶ α ⟶ β
\end{code}
%</type>

Some type results:
%<*weakening>
\begin{code}
lemmaWeakening⊢ :  {Γ Δ : Cxt}{M : Λ}{α : Type}
                →  Γ ⊆ Δ → Γ ⊢ M ∶ α → Δ ⊢ M ∶ α
\end{code}
%</weakening>

\begin{code}
lemmaWeakening⊢ Γ⊆Δ (⊢v x∈Γ) rewrite proj₂ (Γ⊆Δ x∈Γ) 
  = ⊢v (proj₁ (Γ⊆Δ x∈Γ))
lemmaWeakening⊢ Γ⊆Δ (⊢· Γ⊢M:α⟶β Γ⊢N:α) 
  = ⊢· (lemmaWeakening⊢ Γ⊆Δ Γ⊢M:α⟶β) (lemmaWeakening⊢ Γ⊆Δ Γ⊢N:α)
lemmaWeakening⊢ Γ⊆Δ (⊢ƛ Γ,y:α⊢M:β) 
  = ⊢ƛ (lemmaWeakening⊢ (lemma⊆∷ Γ⊆Δ) Γ,y:α⊢M:β)
\end{code}

-- %<*typein>
-- \begin{code}
-- lemmaWeakening⊢∈∷  :  {x : V}{Γ : Cxt}{M : Λ} 
--                    →  x ∈ Γ → Γ ‚ x ⊢ M → Γ ⊢ M
-- \end{code}
-- %</typein>

-- \begin{code}
-- lemmaWeakening⊢∈∷ {x} x∈Γ Γ,x⊢M = lemmaWeakening⊢ (lemmax∈Γ⇒Γ,x⊆Γ x∈Γ) Γ,x⊢M
-- \end{code}

\begin{code}
length : Λ → ℕ
length (v _)   = 1
length (M · N) = length M + length N
length (ƛ x M) = suc (length M)

length>0 : {M : Λ} → length M > zero
length>0 {v x}   = start
                    suc zero
                    ≤⟨ ≤-refl ⟩
                    suc zero
                   ◽
length>0 {M · N} = start
                      suc zero
                      ≤⟨ length>0 {M} ⟩
                      length M
                      ≤⟨ m≤m+n (length M) (length N) ⟩
                      length M + length N
                      ≤⟨ ≤-refl ⟩
                      length (M · N)
                   ◽
length>0 {ƛ x M} = start
                      suc zero 
                      ≤⟨ s≤s z≤n ⟩
                      suc (suc zero)
                      ≤⟨ s≤s (length>0 {M}) ⟩
                      suc (length M)
                      ≤⟨ ≤-refl ⟩
                      length (ƛ x M)
                     ◽
\end{code}

Fresh variable

\begin{code}
data _#_ : V → Λ → Set where
  #v  :  {x y : V}         →  y ≢ x          →  x # v y
  #·  :  {x : V}{M N : Λ}  →  x # M → x # N  →  x # M · N
  #ƛ≡ :  {x : V}{M : Λ}                      →  x # ƛ x M
  #ƛ  :  {x y : V}{M : Λ}  →  x # M          →  x # ƛ y M
\end{code}

-- %<*typefresh>
-- \begin{code}
-- lemma#⊢  :  {x : V}{Γ : Cxt}{M : Λ} 
--          →  x # M → Γ ‚ x ⊢ M → Γ ⊢ M
-- \end{code}
-- %</typefresh>

-- \begin{code}
-- lemma#⊢ (#v y≢x)     (⊢v (here y≡x)) 
--   = ⊥-elim (y≢x y≡x)
-- lemma#⊢ (#v x₂)      (⊢v (there y∈Γ))
--   = ⊢v y∈Γ
-- lemma#⊢ (#· x#M x#N) (⊢· Γ,x⊢M Γ,x⊢N) 
--   = ⊢· (lemma#⊢ x#M Γ,x⊢M) (lemma#⊢ x#N Γ,x⊢N)
-- lemma#⊢ #ƛ≡          (⊢ƛ Γ,x,x⊢M) 
--   = ⊢ƛ (lemmaWeakening⊢∈∷ (here refl) Γ,x,x⊢M)
-- lemma#⊢ (#ƛ x#M)     (⊢ƛ Γ,x,y⊢M) 
--   = ⊢ƛ (lemma#⊢ x#M (lemmaWeakening⊢ lemmaΓ,x,y⊆Γ,y,x Γ,x,y⊢M))
-- \end{code}

\begin{code}
_∼#_ : (M M' : Λ) → Set
_∼#_ M M' = (∀ x → x # M → x # M') × (∀ x → x # M' → x # M)
\end{code}

Variable Ocurr free in a term.

\begin{code}
data _*_ : V → Λ → Set where
  *v   :  {x : V}                           → x * v x
  *·l  :  {x : V}{M N : Λ} → x * M          → x * M · N
  *·r  :  {x : V}{M N : Λ} → x * N          → x * M · N
  *ƛ   :  {x y : V}{M : Λ} → x * M → y ≢ x  → x * ƛ y M
\end{code}

-- -- \begin{code}
-- -- lemma*⊢ : {M N : Λ}{x : V} → x * M → Γ ⊢ M → x ∈ Γ
-- -- \end{code}

\begin{code}
_#?_ : Decidable _#_
x #? (v y) with y ≟ x
... | yes y≡x = no (λ {(#v y≢x) → y≢x y≡x})
... | no  y≢x = yes (#v y≢x)
x #? (M · N) with x #? M | x #? N 
... | yes x#M | yes  x#N = yes (#· x#M x#N)
... | yes x#M | no  ¬x#N = no (λ {(#· _ x#N) → ¬x#N x#N})
... | no ¬x#M | yes  x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
... | no ¬x#M | no  ¬x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
x #? (ƛ y M) with y | x ≟ y 
... | .x | yes refl = yes #ƛ≡
... | _  | no  x≢y with x #? M
...                | yes  x#M = yes (#ƛ x#M) 
x #? (ƛ y M) 
    | w  | no  x≢w | no  ¬x#M = no (aux x≢w ¬x#M)
  where aux : {x w : V} → x ≢ w → ¬ (x # M) →  x # ƛ w M → ⊥
        aux x≢w ¬x#ƛwM #ƛ≡         =  ⊥-elim (x≢w refl)
        aux x≢w ¬x#ƛwM (#ƛ x#ƛwM)  =  ⊥-elim (¬x#ƛwM x#ƛwM)

lemma¬#→free : {x : V}{M : Λ} → ¬ (x # M) → x * M
lemma¬#→free {x} {v y} ¬x#M with y ≟ x
... | no  y≢x   = ⊥-elim (¬x#M (#v y≢x))
lemma¬#→free {x} {v .x} ¬x#M 
    | yes refl  = *v
lemma¬#→free {x} {M · N} ¬x#MN with x #? M | x #? N 
... | yes x#M | yes x#N = ⊥-elim (¬x#MN (#· x#M x#N))
... | yes x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
... | no ¬x#M | yes x#N = *·l (lemma¬#→free ¬x#M)
... | no ¬x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
lemma¬#→free {x} {ƛ y M} ¬x#λxM with y ≟ x
... | no  y≢x with x #? M
... | yes x#M = ⊥-elim (¬x#λxM (#ƛ x#M))
... | no ¬x#M = *ƛ (lemma¬#→free ¬x#M) y≢x
lemma¬#→free {x} {ƛ .x M} ¬x#λxM 
    | yes refl = ⊥-elim (¬x#λxM #ƛ≡)
--
lemma-free→¬# : {x : V}{M : Λ} → x * M →  ¬ (x # M)
lemma-free→¬# {x} {v .x} *v            (#v x≢x) 
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {M · N} (*·l xfreeM) (#· x#M x#N) 
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
lemma-free→¬# {x} {M · N} (*·r xfreeN) (#· x#M x#N) 
  = ⊥-elim ((lemma-free→¬# xfreeN) x#N)
lemma-free→¬# {x} {ƛ .x M} (*ƛ xfreeM x≢x) #ƛ≡
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {ƛ y M} (*ƛ xfreeM y≢x) (#ƛ x#M)  
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
--
lemma#→¬free : {x : V}{M : Λ} → x # M → ¬ (x * M)
lemma#→¬free x#M x*M = ⊥-elim ((lemma-free→¬# x*M) x#M)
\end{code}}

Sameness of free variables is an important relation between terms, which is defined as follows:

\begin{code}
_∼*_ : (M M' : Λ) → Set
_∼*_ M M' = (∀ x → x * M → x * M') × (∀ x → x * M' → x * M)
\end{code}

%<*typeweakening#>
\begin{code}
lemmaWeakening⊢#  : {Γ : Cxt}{M : Λ}{x : V}{α β : Type} 
                  → x # M → Γ ⊢ M ∶ α → Γ ‚ x ∶ β ⊢ M ∶ α
\end{code}
%</typeweakening#>

\begin{code}
lemmaWeakening⊢# (#v y≢x)      (⊢v y∈Γ)          
  = ⊢v (there (⊥-elim ∘ y≢x) y∈Γ) 
lemmaWeakening⊢# (#· x#M x#N)  (⊢· Γ⊢M∶α⟶β Γ⊢N∶α)  
  = ⊢· (lemmaWeakening⊢# x#M Γ⊢M∶α⟶β) (lemmaWeakening⊢# x#N Γ⊢N∶α)
lemmaWeakening⊢# {M = ƛ y M} {x = x} x#ƛyM (⊢ƛ Γ,y↦β⊢M∶α) 
  with x#ƛyM  | y ≟ x 
... | #ƛ x#M  | no   y≢x   
  = ⊢ƛ (lemmaWeakening⊢ (lemma⊆xy y≢x) (lemmaWeakening⊢# x#M Γ,y↦β⊢M∶α))
lemmaWeakening⊢# {M = ƛ .x M} {x = x} x#ƛyM (⊢ƛ Γ,x↦β⊢M∶α) 
    | #ƛ≡     | no   y≢x   
  = ⊥-elim (y≢x refl)
lemmaWeakening⊢# {M = ƛ .x M} {x = x} x#ƛyM (⊢ƛ Γ,x↦β⊢M∶α) 
    | _       | yes  refl  
  = ⊢ƛ (lemmaWeakening⊢ lemma⊆x Γ,x↦β⊢M∶α)
\end{code}

-- %<*typeStrengthening> 
-- \begin{code}
-- lemmaStrengthening⊢#  : {Γ : Cxt}{M : Λ}{x : V}{α : Type} 
--                       → x # M → Γ ⊢ M ∶ α → Γ \\ x ⊢ M ∶ α 
-- \end{code}
-- %</typeStrengthening>

-- \begin{code}
-- lemmaStrengthening⊢# (#v y≢x) (⊢v y∈Γ) 
--   with lemma\\← y≢x y∈Γ
-- ... | y∈Γ\\x ∶ Γ⟨y∈Γ⟩≡Γ\\⟨y∈Γ\\x⟩
--   rewrite Γ⟨y∈Γ⟩≡Γ\\⟨y∈Γ\\x⟩
--   = ⊢v y∈Γ\\x
-- lemmaStrengthening⊢# (#· x#M x#N) (⊢· Γ⊢M∶α⟶β Γ⊢N∶α) 
--   = ⊢· (lemmaStrengthening⊢# x#M Γ⊢M∶α⟶β) (lemmaStrengthening⊢# x#N Γ⊢N∶α)  
-- lemmaStrengthening⊢# x#M (⊢ƛ Γ,y:α⊢M∶β) 
--   = {!!}
-- \end{code}

%<*typeStrengthening> 
\begin{code}
-- postulate
--    lemmaStrengthening⊢,#  : {Γ : Cxt}{M : Λ}{x : V}{α β : Type} 
--                           → x # M → Γ  ⊢ M ∶ α → Γ ‚ x ∶ β ⊢ M ∶ α 

lemma⊢*∈  : {Γ : Cxt}{M : Λ}{x : V}{α : Type} 
          → Γ ⊢ M ∶ α → x * M → x ∈ Γ
lemma⊢*∈ (⊢v x∈Γ)             *v            = x∈Γ
lemma⊢*∈ (⊢· Γ⊢M:α⟶β Γ⊢N:α)  (*·l x*M)     = lemma⊢*∈ Γ⊢M:α⟶β x*M
lemma⊢*∈ (⊢· Γ⊢M:α⟶β Γ⊢N:α)  (*·r x*N)     = lemma⊢*∈ Γ⊢N:α x*N
lemma⊢*∈ (⊢ƛ Γ,y:α⊢M:β)       (*ƛ x*M y≢x) with lemma⊢*∈ Γ,y:α⊢M:β x*M
... | here x≡y     = ⊥-elim (y≢x (sym x≡y))
... | there _ x∈Γ  = x∈Γ

-- lemmaStrengthening⊢⊆#  : {Γ : Cxt}{M : Λ}{α : Type} 
--                        → Γ ⊢ M ∶ α → Σₓ Cxt (λ Δ → (Δ ⊢ M ∶ α) × (Δ ⊆ Γ) × ((x : V) → x ∈ Δ → x * M))
-- lemmaStrengthening⊢⊆# {[]}                Γ⊢M∶α = [] ∶  Γ⊢M∶α ∶  ρ⊆ ∶ λ x ()
-- lemmaStrengthening⊢⊆# {(x ∶ β) ∷ Γ}  {M}  Γ,x:β⊢M∶α 
--   with x #? M
-- ... | no ¬x#M  = {!!} 
-- ... | yes x#M  with lemmaStrengthening⊢⊆# {Γ} {M} (lemmaStrengthening⊢,# x#M Γ,x:β⊢M∶α)
-- ...            | Δ ∶ Δ⊢M∶α ∶ Δ⊆Γ ∶ ∀x→x∈Δ→x*M 
--   = Δ ∶ Δ⊢M∶α ∶ Δ⊆Γ,x∶β ∶ ∀x→x∈Δ→x*M 
--   where
--   Δ⊆Γ,x∶β : Δ ⊆ Γ ‚ x ∶ β
--   Δ⊆Γ,x∶β  {z} z∈Δ with z ≟ x
--   ... | no  z≢x   = there z≢x (proj₁ (Δ⊆Γ z∈Δ)) ∶ proj₂ (Δ⊆Γ z∈Δ)
--   Δ⊆Γ,x∶β  .{x} x∈Δ 
--       | yes refl  = ⊥-elim ((lemma#→¬free x#M) (∀x→x∈Δ→x*M x x∈Δ))
\end{code}
%</typeStrengthening>

